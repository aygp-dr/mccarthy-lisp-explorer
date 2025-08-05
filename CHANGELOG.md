# Changelog

## [0.1.0] - 2025-08-05

Initial release of McCarthy's Lisp Explorer.

### Added
- Complete implementation of McCarthy's five primitive functions (atom, eq, car, cdr, cons)
- Universal evaluator implementation (eval/apply)
- Core higher-level functions (equal, append, assoc, list, etc.)
- Mathematical functions (factorial, GCD, sqrt approximation)
- Comprehensive test suite with both Scheme and Coq proofs
- Educational materials:
  - Reading guide for McCarthy's 1960 paper
  - Interactive examples
  - Structured exercises
  - Presentation materials for teaching
- Literate programming support with Org-mode
- Documentation for all major components
- FreeBSD and GNU/Linux compatibility

### Technical Details
- Built with GNU Guile Scheme 3.0+
- Formal verification with Coq
- Makefile automation for common tasks
- Module system following Guile conventions