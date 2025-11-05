import { Rule, Scope } from 'eslint'
import ESTree from 'estree'
import {
  dereference,
  findParent,
  getStringValue,
  isStringNode,
  StringNode,
} from '../utils/ast.js'
import { createRule } from '../utils/createRule.js'
import { parseFnCall } from '../utils/parseFnCall.js'

const doesBinaryExpressionContainStringNode = (
  binaryExp: ESTree.BinaryExpression,
): boolean => {
  if (isStringNode(binaryExp.right)) {
    return true
  }

  if (binaryExp.left.type === 'BinaryExpression') {
    return doesBinaryExpressionContainStringNode(binaryExp.left)
  }

  return isStringNode(binaryExp.left)
}

const quoteStringValue = (node: StringNode): string =>
  node.type === 'TemplateLiteral'
    ? `\`${node.quasis[0].value.raw}\``
    : node.raw ?? ''

const compileMatcherPattern = (
  matcherMaybeWithMessage: MatcherAndMessage | string,
): CompiledMatcherAndMessage => {
  const [matcher, message] = Array.isArray(matcherMaybeWithMessage)
    ? matcherMaybeWithMessage
    : [matcherMaybeWithMessage]

  return [new RegExp(matcher, 'u'), message]
}

const compileMatcherPatterns = (
  matchers:
    | Partial<Record<MatcherGroups, string | MatcherAndMessage>>
    | MatcherAndMessage
    | string,
): Record<MatcherGroups, CompiledMatcherAndMessage | null> &
  Record<string, CompiledMatcherAndMessage | null> => {
  if (typeof matchers === 'string' || Array.isArray(matchers)) {
    const compiledMatcher = compileMatcherPattern(matchers)

    return {
      describe: compiledMatcher,
      step: compiledMatcher,
      test: compiledMatcher,
    }
  }

  return {
    describe: matchers.describe
      ? compileMatcherPattern(matchers.describe)
      : null,
    step: matchers.step ? compileMatcherPattern(matchers.step) : null,
    test: matchers.test ? compileMatcherPattern(matchers.test) : null,
  }
}

type CompiledMatcherAndMessage = [matcher: RegExp, message?: string]
type MatcherAndMessage = [matcher: string, message?: string]

const MatcherAndMessageSchema = {
  additionalItems: false,
  items: { type: 'string' },
  maxItems: 2,
  minItems: 1,
  type: 'array',
} as const

type MatcherGroups = 'describe' | 'step' | 'test'

/**
 * Checks if an array element's 'name' property is a string literal or simple
 * template literal.
 */
const hasStringNameProperty = (
  element: ESTree.Expression | ESTree.SpreadElement | null,
): boolean => {
  if (!element || element.type !== 'ObjectExpression') {
    return false
  }

  const nameProperty = element.properties.find((prop) => {
    if (prop.type !== 'Property' || prop.key.type !== 'Identifier') {
      return false
    }
    return prop.key.name === 'name'
  })

  if (!nameProperty || nameProperty.type !== 'Property') {
    return false
  }

  return isStringNode(nameProperty.value)
}

/**
 * Pattern A: Checks if an identifier comes from a for-of loop destructuring
 * pattern and if the array elements have string 'name' properties.
 */
const isForOfDestructuringPattern = (
  context: Rule.RuleContext,
  title: ESTree.Identifier,
): boolean => {
  // Find the ForOfStatement that contains this identifier
  const forOfStatement = findParent(title, 'ForOfStatement')
  if (!forOfStatement) {
    return false
  }

  // Verify the identifier is within the loop body
  const body = forOfStatement.body
  if (!body.range || !title.range) {
    return false
  }
  // Check if the identifier is within the body's range
  if (title.range[0] < body.range[0] || title.range[1] > body.range[1]) {
    return false
  }

  // Check the left side of the for-of statement
  const left = forOfStatement.left
  let objectPattern: ESTree.ObjectPattern | null = null

  if (left.type === 'VariableDeclaration') {
    const declarator = left.declarations[0]
    if (!declarator || declarator.id.type !== 'ObjectPattern') {
      return false
    }
    objectPattern = declarator.id
  } else if (left.type === 'ObjectPattern') {
    objectPattern = left
  } else {
    return false
  }

  // Check if the title identifier is destructured from the pattern
  const property = objectPattern.properties.find(
    (prop) =>
      prop.type === 'Property' &&
      prop.value.type === 'Identifier' &&
      prop.value.name === title.name,
  )
  if (!property) {
    return false
  }

  // Resolve the right-hand side (the array identifier)
  const right = forOfStatement.right
  if (right.type !== 'Identifier') {
    return false
  }

  // Try to find the variable declaration by traversing scopes
  let arrayInit: ESTree.Node | undefined
  let scope: Scope.Scope | null = context.sourceCode.getScope(right)

  while (scope && !arrayInit) {
    const variable = scope.variables.find((v) => v.name === right.name)
    if (variable && variable.defs.length > 0) {
      const def = variable.defs[0]
      if (def.node.type === 'VariableDeclarator' && def.node.init) {
        arrayInit = def.node.init
        break
      }
    }
    scope = scope.upper
  }

  // Fallback to dereference if scope traversal didn't work
  if (!arrayInit) {
    const derefResult = dereference(context, right)
    if (derefResult && 'type' in derefResult) {
      arrayInit = derefResult as ESTree.Node
    }
  }

  if (!arrayInit || arrayInit.type !== 'ArrayExpression') {
    return false
  }

  // Check if all elements have string 'name' properties
  // We check all elements to be conservative
  if (arrayInit.elements.length === 0) {
    return false
  }

  return arrayInit.elements.every(hasStringNameProperty)
}

/**
 * Pattern B: Checks if a MemberExpression is an array index access pattern
 * (e.g., cases[0].name) and if the array element has a string 'name' property.
 */
const isArrayIndexAccessPattern = (
  context: Rule.RuleContext,
  title: ESTree.MemberExpression,
): boolean => {
  // Must be a property access like cases[0].name
  if (title.property.type !== 'Identifier') {
    return false
  }

  const propertyName = title.property.name
  if (propertyName !== 'name') {
    return false
  }

  // The object must be a MemberExpression with array access
  if (title.object.type !== 'MemberExpression') {
    return false
  }

  const arrayAccess = title.object

  // Check if it's computed property access (array[index])
  if (!arrayAccess.computed) {
    return false
  }

  const index = arrayAccess.property
  // Index should be a numeric literal or string literal that can be converted to a number
  let arrayIndex: number | null = null
  if (index.type === 'Literal') {
    if (typeof index.value === 'number') {
      arrayIndex = index.value
    } else if (typeof index.value === 'string' && /^\d+$/.test(index.value)) {
      arrayIndex = parseInt(index.value, 10)
    }
  }

  if (arrayIndex === null) {
    // If index is not a literal, we could check if all elements have string names
    // but that's more complex. For now, be conservative and only accept literal indices.
    return false
  }

  // Resolve the array identifier
  const arrayIdentifier = arrayAccess.object
  if (arrayIdentifier.type !== 'Identifier') {
    return false
  }

  const arrayInit = dereference(context, arrayIdentifier)
  if (!arrayInit || arrayInit.type !== 'ArrayExpression') {
    return false
  }

  // Check bounds
  if (arrayIndex < 0 || arrayIndex >= arrayInit.elements.length) {
    return false
  }

  // Check if the specific element has a string 'name' property
  const element = arrayInit.elements[arrayIndex]
  return hasStringNameProperty(element)
}

interface Options {
  disallowedWords?: string[]
  ignoreSpaces?: boolean
  ignoreTypeOfDescribeName?: boolean
  ignoreTypeOfStepName?: boolean
  ignoreTypeOfTestName?: boolean
  mustMatch?:
    | Partial<Record<MatcherGroups, string | MatcherAndMessage>>
    | MatcherAndMessage
    | string
  mustNotMatch?:
    | Partial<Record<MatcherGroups, string | MatcherAndMessage>>
    | MatcherAndMessage
    | string
}

export default createRule({
  create(context) {
    const opts: Options = context.options?.[0] ?? {}
    const {
      disallowedWords = [],
      ignoreSpaces = false,
      ignoreTypeOfDescribeName = false,
      ignoreTypeOfStepName = true,
      ignoreTypeOfTestName = false,
      mustMatch,
      mustNotMatch,
    } = opts
    const disallowedWordsRegexp = new RegExp(
      `\\b(${disallowedWords.join('|')})\\b`,
      'iu',
    )

    const mustNotMatchPatterns = compileMatcherPatterns(mustNotMatch ?? {})
    const mustMatchPatterns = compileMatcherPatterns(mustMatch ?? {})

    return {
      CallExpression(node) {
        const call = parseFnCall(context, node)
        if (
          call?.type !== 'test' &&
          call?.type !== 'describe' &&
          call?.type !== 'step'
        ) {
          return
        }

        const [argument] = node.arguments
        const title = dereference(context, argument) ?? argument
        if (!title) return

        if (!isStringNode(title)) {
          if (
            title.type === 'BinaryExpression' &&
            doesBinaryExpressionContainStringNode(title)
          ) {
            return
          }

          // AST-only inference: Check for for-of destructuring pattern
          // Check the original argument, not the dereferenced title
          if (
            argument.type === 'Identifier' &&
            isForOfDestructuringPattern(context, argument)
          ) {
            // Valid: title comes from destructuring a cases array with string names
            return
          }

          // AST-only inference: Check for array index access pattern
          // Check the original argument, not the dereferenced title
          if (
            argument.type === 'MemberExpression' &&
            isArrayIndexAccessPattern(context, argument)
          ) {
            // Valid: title comes from array access like cases[0].name
            return
          }

          if (
            !(
              (call.type === 'describe' && ignoreTypeOfDescribeName) ||
              (call.type === 'test' && ignoreTypeOfTestName) ||
              (call.type === 'step' && ignoreTypeOfStepName)
            ) &&
            (title as ESTree.Node).type !== 'TemplateLiteral'
          ) {
            context.report({
              loc: title.loc!,
              messageId: 'titleMustBeString',
            })
          }

          return
        }

        const titleString = getStringValue(title)
        const functionName = call.type

        if (!titleString) {
          context.report({
            data: { functionName: call.type },
            messageId: 'emptyTitle',
            node,
          })

          return
        }

        if (disallowedWords.length > 0) {
          const disallowedMatch = disallowedWordsRegexp.exec(titleString)

          if (disallowedMatch) {
            context.report({
              data: { word: disallowedMatch[1] },
              messageId: 'disallowedWord',
              node: title,
            })

            return
          }
        }

        if (
          ignoreSpaces === false &&
          titleString.trim().length !== titleString.length
        ) {
          context.report({
            fix: (fixer) => [
              fixer.replaceTextRange(
                title.range!,
                quoteStringValue(title)
                  .replace(/^([`'"]) +?/u, '$1')
                  .replace(/ +?([`'"])$/u, '$1'),
              ),
            ],
            messageId: 'accidentalSpace',
            node: title,
          })
        }

        const [firstWord] = titleString.split(' ')
        if (firstWord.toLowerCase() === functionName) {
          context.report({
            fix: (fixer) => [
              fixer.replaceTextRange(
                title.range!,
                quoteStringValue(title).replace(/^([`'"]).+? /u, '$1'),
              ),
            ],
            messageId: 'duplicatePrefix',
            node: title,
          })
        }

        const [mustNotMatchPattern, mustNotMatchMessage] =
          mustNotMatchPatterns[functionName] ?? []

        if (mustNotMatchPattern && mustNotMatchPattern.test(titleString)) {
          context.report({
            data: {
              functionName,
              message: mustNotMatchMessage ?? '',
              pattern: String(mustNotMatchPattern),
            },
            messageId: mustNotMatchMessage
              ? 'mustNotMatchCustom'
              : 'mustNotMatch',
            node: title,
          })

          return
        }

        const [mustMatchPattern, mustMatchMessage] =
          mustMatchPatterns[functionName] ?? []

        if (mustMatchPattern && !mustMatchPattern.test(titleString)) {
          context.report({
            data: {
              functionName,
              message: mustMatchMessage ?? '',
              pattern: String(mustMatchPattern),
            },
            messageId: mustMatchMessage ? 'mustMatchCustom' : 'mustMatch',
            node: title,
          })

          return
        }
      },
    }
  },
  meta: {
    docs: {
      category: 'Best Practices',
      description: 'Enforce valid titles',
      recommended: true,
      url: 'https://github.com/playwright-community/eslint-plugin-playwright/tree/main/docs/rules/valid-title.md',
    },
    fixable: 'code',
    messages: {
      accidentalSpace: 'should not have leading or trailing spaces',
      disallowedWord: '"{{ word }}" is not allowed in test titles',
      duplicatePrefix: 'should not have duplicate prefix',
      emptyTitle: '{{ functionName }} should not have an empty title',
      mustMatch: '{{ functionName }} should match {{ pattern }}',
      mustMatchCustom: '{{ message }}',
      mustNotMatch: '{{ functionName }} should not match {{ pattern }}',
      mustNotMatchCustom: '{{ message }}',
      titleMustBeString: 'Title must be a string',
    },
    schema: [
      {
        additionalProperties: false,
        patternProperties: {
          [/^must(?:Not)?Match$/u.source]: {
            oneOf: [
              { type: 'string' },
              MatcherAndMessageSchema,
              {
                additionalProperties: {
                  oneOf: [{ type: 'string' }, MatcherAndMessageSchema],
                },
                propertyNames: { enum: ['describe', 'test', 'step'] },
                type: 'object',
              },
            ],
          },
        },
        properties: {
          disallowedWords: {
            items: { type: 'string' },
            type: 'array',
          },
          ignoreSpaces: {
            default: false,
            type: 'boolean',
          },
          ignoreTypeOfDescribeName: {
            default: false,
            type: 'boolean',
          },
          ignoreTypeOfStepName: {
            default: true,
            type: 'boolean',
          },
          ignoreTypeOfTestName: {
            default: false,
            type: 'boolean',
          },
        },
        type: 'object',
      },
    ],
    type: 'suggestion',
  },
})
