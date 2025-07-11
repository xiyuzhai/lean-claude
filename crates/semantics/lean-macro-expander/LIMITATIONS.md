# Macro System Limitations and Known Issues

This document tracks the current limitations and known issues with the macro expansion system.

## Working Features ✅

1. **Basic macro definitions** - `macro "name" x:term : term => body`
2. **Macro rules with patterns** - `macro_rules | pattern => body`
3. **Antiquotations** - `$x` in patterns and templates
4. **Splices** - `$xs,*` for list patterns
5. **Nested macro expansion** - Macros calling other macros
6. **Pattern matching** - Multiple rules with pattern matching
7. **Basic hygiene** - Fresh name generation for macro-introduced identifiers

## Current Limitations ❌

### 1. Parser Limitations

- **Unit syntax `()`** - Not recognized as Unit.unit
- **Custom operators** - Operators like `??` in patterns aren't supported
- **Do notation** - `do` blocks with bind operator `←` not parsed
- **Multiple parameters with keywords** - Patterns like `x:term "with" t:tactic`
- **Binder syntax in patterns** - Complex binder patterns not fully supported

### 2. Expansion Limitations

- **Nested quotations** - `` `(`($x)) `` style nested quotations
- **Category restrictions** - Mixed category macros (term/tactic/command) have limited support
- **Hygiene for let bindings** - Let-bound names may conflict in some cases

### 3. Missing Features

- **Macro scoping** - No namespace/section support for macros
- **Precedence** - Custom operator precedence not implemented
- **Elaboration** - No type checking during expansion
- **Error messages** - Limited error reporting for macro failures

## Test Coverage

### Passing Tests ✅
- Basic macro expansion
- Pattern matching with macro_rules
- List splices and recursion
- Nested macro calls
- Multiple pattern rules
- Performance (100 macros < 1ms)

### Failing Tests ❌
- Hygiene with let bindings
- Complex binder patterns
- Custom operator patterns
- Do notation
- Mixed category macros

## Next Steps

1. **Fix parser issues**
   - Add support for unit `()` syntax
   - Implement custom operator parsing in patterns
   - Add do notation with bind operator

2. **Improve expansion**
   - Better hygiene for all binding forms
   - Support nested quotations
   - Handle mixed categories properly

3. **Add missing features**
   - Macro scoping rules
   - Better error messages
   - Integration with elaborator

## Example Failures

```lean
-- Fails: () not recognized
macro_rules | `() => `(Unit.unit)

-- Fails: Custom operator
macro_rules | `($x ?? $y) => `(...)  

-- Fails: Do notation
do let x ← getValue; ...

-- Fails: Mixed categories
macro "m" x:term "with" t:tactic : command => ...
```