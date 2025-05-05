# Implementation Guide

This document explains our implementation of McCarthy's LISP evaluator using Guile Scheme.

## Setup

First, ensure you have Guile Scheme installed:

```bash
# On Debian/Ubuntu
sudo apt install guile-3.0

# On macOS with Homebrew
brew install guile

# On Windows via MSYS2
pacman -S mingw-w64-x86_64-guile
```

## Running the Examples

Each example file can be run directly with Guile:

```bash
guile examples/hello-world.scm
guile examples/factorial.scm
guile examples/mccarthy-examples.scm
```

## Structure of the Implementation

Our implementation follows McCarthy's paper closely but uses Scheme's native syntax and features when convenient.

### S-expressions (s-expressions.scm)

This file defines McCarthy's five primitive operations:
- `mccarthy-atom?`
- `mccarthy-eq?`
- `mccarthy-car`
- `mccarthy-cdr`
- `mccarthy-cons`

### Core Functions (core.scm)

This file implements higher-level functions from the paper:
- `sublis` (substitution)
- `mccarthy-null?`
- `mccarthy-equal?`
- `mccarthy-append`
- `mccarthy-pair`
- Association list functions

### Evaluator (evaluator.scm)

This file implements the eval/apply evaluator from section 4 of the paper:
- `eval` - Evaluates expressions
- `apply` - Applies functions to arguments
- `evcon` - Evaluates conditionals
- `evlis` - Evaluates lists of expressions

## Key Differences from McCarthy's Original

1. **Scheme vs. M-expressions**: McCarthy used M-expression syntax, while we use Scheme's S-expression syntax.
2. **Built-in Functions**: We use some of Scheme's built-in functions for convenience.
3. **Error Handling**: We've added error messages that weren't in the original.
4. **Environment**: Our environment structure is slightly different.

## Implementation Notes

- McCarthy's approach is surprisingly simple yet powerful.
- The eval/apply recursion beautifully demonstrates how a language can evaluate itself.
- The core insight of treating code as data via S-expressions remains revolutionary.
- The evaluator is a complete implementation of a Lisp-like language in just a few dozen lines of code.

## Extending the Implementation

To extend this implementation:
1. Add more primitive functions to the `primitive-functions` list
2. Implement macros as described in later Lisp papers
3. Add a proper lexical scope mechanism
4. Implement a garbage collector
5. Add a reader/printer to parse and display S-expressions
