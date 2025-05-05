# McCarthy Lisp Explorer Implementation Guide

This document describes how the implementation in this repository corresponds to McCarthy's 1960 paper "Recursive Functions of Symbolic Expressions and Their Computation by Machine, Part I."

## Design Philosophy

Our implementation follows several key principles:

1. **Fidelity to the original paper** - We strive to implement the functions exactly as McCarthy described them, using the same names and semantics.
2. **Clarity over efficiency** - We prioritize readability and understanding over performance.
3. **Minimalism** - We implement only what's necessary to demonstrate the core concepts.
4. **Pedagogical value** - The code should help readers understand McCarthy's paper.

## Core Implementation

The core implementation is found in `src/ap/mccarthy/core-functions.scm`. This file implements:

### Five Elementary Functions (Section 3c)

McCarthy's paper defines five basic operations on S-expressions:

1. `atom?` - Tests if an expression is an atomic symbol
2. `eq?` - Tests if two atomic symbols are identical
3. `car` - Returns the first element of a list
4. `cdr` - Returns the rest of a list
5. `cons` - Constructs a new list by adding an element to the front

Our implementation provides these exactly as McCarthy described them.

### Higher-level Functions (Section 3d)

The paper defines several useful functions built on top of the primitives:

- `null?` - Tests if a list is empty
- `equal?` - Tests if two S-expressions are structurally identical
- `append` - Joins two lists
- `pair` - Creates a list of pairs
- `assoc` - Finds an association in an association list

### Mathematical Functions (Section 3e)

McCarthy demonstrates the power of recursive definitions with several mathematical functions:

- `factorial` - Computes the factorial of a number
- `gcd-recursive` - Computes the greatest common divisor
- `sqrt-approx` - Approximates the square root using Newton's method

## Universal Evaluator

The universal evaluator, described in Section 4, is implemented in `src/ap/mccarthy/evaluator.scm`. This includes:

- `eval` - Evaluates S-expressions
- `apply` - Applies functions to arguments
- `evlis` - Evaluates a list of expressions
- `evcon` - Evaluates conditional expressions

The evaluator demonstrates how Lisp can interpret programs represented as S-expressions.

## Implementation Notes

### Differences from McCarthy's Paper

While we strive for fidelity, a few differences exist:

1. **Error handling** - We provide better error messages than would have been possible in 1960.
2. **Guile features** - We use Guile Scheme's module system for organization.
3. **Tracing support** - We add tracing features for educational purposes.

### Extending the Implementation

This implementation can be extended in several ways:

1. Add more functions from LISP 1.5
2. Implement property lists for symbols
3. Add a simple compiler to lower-level operations
4. Create a reader for textual S-expressions

## Using the Implementation

### Basic Usage

```scheme
(use-modules (ap mccarthy))

;; Use the five primitives
(atom? 'A)              ; => #t
(eq? 'A 'A)             ; => #t
(car '(A B C))          ; => A
(cdr '(A B C))          ; => (B C)
(cons 'A '(B C))        ; => (A B C)

;; Use higher-level functions
(equal? '(A B C) '(A B C))  ; => #t
(append '(A B) '(C D))      ; => (A B C D)

;; Use the evaluator
(eval '(car '(A B C)) '())  ; => A
```

### Tracing

Enable tracing to see how recursive functions work:

```scheme
(trace-on)
(factorial 5)  ; Shows the recursive steps
(trace-off)
```

## Related Files

- `examples/hello-world.scm` - Simple introduction to S-expressions
- `examples/factorial.scm` - Implementation of factorial
- `examples/math-functions.scm` - Mathematical functions from Section 3
- `examples/mccarthy-examples.scm` - Direct examples from the paper
- `interactive-examples.scm` - Interactive tour of the key concepts