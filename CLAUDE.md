#+TITLE: CLAUDE.org Guide for this Repository
#+AUTHOR: 
#+DATE: 
#+OPTIONS: toc:2

* Build/Test/Lint Commands

** Python
- Test: =pytest {file_path}= or =pytest -xvs {file_path}::test_name= for single tests
- Environment: =poetry install= and =poetry shell= for Poetry projects

** JavaScript/Node
- Test: =npm test= or =npm test -- -t "test name"= for single tests
- Lint: =eslint .= for JS

** Make-based
- Check local Makefile (=gmake help= or =make test=)

** Linting
- Python: =black .=
- Multi-language: =pre-commit run --all-files=

* Code Style Guidelines

** Formatting
- Python: Use Black with default settings
- JS/TS: Prettier with 2-space indentation

** Imports
- Group imports (stdlib, third-party, local) with one blank line between groups

** Types
- Use type annotations in Python
- Use TypeScript for JS projects

** Naming
- Python: snake_case for variables, PascalCase for classes
- JS: camelCase for variables, PascalCase for classes

** Error handling
- Use try/except with specific exceptions
- Ensure proper error propagation

** Documentation
- Write docstrings (Google style) for functions
- Include examples when possible

** Tests
- Write unit tests for all new functionality
- Aim for >80% coverage

* IMPORTANT: Git Commit Guidelines

** Conventional Commits
Use conventional commits format:
: <type>(<scope>): <description>

- =type=: feat, fix, docs, style, refactor, perf, test, build, ci, chore
- =scope=: optional component name (in parentheses)
- =description=: imperative, present tense (e.g., "add" not "added" or "adds")

Examples:
: feat(parser): add ability to parse arrays
: fix(middleware): correct memory leak issue
: docs(readme): update installation instructions

** Co-authoring and Reviews
For co-authoring and reviews, use git trailer syntax:

For co-authors:
: git commit -m "feat: implement feature X" --trailer "Co-authored-by: Name <email@example.com>"

For reviewers:
: git commit -m "fix: resolve bug Y" --trailer "Reviewed-by: Name <email@example.com>"

Multiple trailers can be added:
: git commit -m "docs: update README" \
:   --trailer "Co-authored-by: Name1 <email1@example.com>" \
:   --trailer "Reviewed-by: Name2 <email2@example.com>"

* Project Organization
- Use =resources/= for downloaded reference materials
- Use =src/= for source code
- Use =examples/= for example code
- Use =tests/= for test cases
- Use =docs/= for documentation

When unsure, follow the existing conventions in the repository.