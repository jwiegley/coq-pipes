# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Overview

This is a formalization in Coq of the Haskell pipes library, proving nearly all its laws. The project demonstrates mechanized proofs of category theory laws for streaming computations.

## Build Commands

```bash
# Build all Coq files
make

# Generate Makefile.coq from _CoqProject
coq_makefile -f _CoqProject -o Makefile.coq

# Build a specific .vo file
make src/Pipes/Core.vo

# Clean build artifacts
make clean

# Generate PDF documentation (requires LaTeX)
make coq-pipes.pdf
```

## Development Commands

```bash
# Check for admitted/undefined proofs
find src -name '*.v' \( ! -name Extract.v -print \) | xargs egrep -i -Hn '(abort|admit|undefined)' | egrep -v 'Definition undefined'

# Interactive Coq development
coqide src/Pipes/Core.v  # or use Proof General/CoqIDE
```

## Code Architecture

### Module Structure

The codebase uses a layered architecture with dependencies flowing upward:

1. **Pipes.Internal** - Core `Proxy` type definition using the Yoneda lemma to satisfy Coq's strict positivity requirement. Defines the fundamental `foldProxy` operation and basic instances (Functor, Applicative, Monad).

2. **Pipes.Core** - Category operations for pipes:
   - Request/Respond categories (`\>\`, `/>/`)
   - Push/Pull categories (`>~>`, `>+>`)
   - The `reflect` duality operation
   - Identity and composition laws for each category

3. **Pipes** - High-level user interface:
   - `yield`, `await`, `cat` combinators
   - Connection operators (`>->`, `>~`)
   - Producer/Consumer type aliases
   - `for` and `each` iteration constructs

4. **Pipes.Prelude** - Library functions like `map`, `filter`, `take`, `drop`, `toListM`

5. **Pipes.Extras** - Additional utilities and theorems

### Key Design Decisions

- **Fuel-based recursion**: `push` and `pull` use a fuel parameter to make them structurally recursive, with axioms asserting infinite fuel availability. This compromise allows inductive definitions while maintaining semantic infiniteness.

- **Yoneda embedding**: The `Proxy` type uses existential quantification instead of universal to satisfy strict positivity, following the contravariant Yoneda lemma.

- **Proof organization**: Laws are proven as Coq Obligations where possible, with explicit theorems for distribution and composition properties.

## Dependencies

- **coq-haskell**: Required library for Haskell-like abstractions in Coq
- Coq version compatible with the coq-haskell library

## Project Structure

```
_CoqProject     - Coq project configuration (-R src P)
src/
  Pipes.v       - Main user-facing module
  Pipes/
    Internal.v  - Core Proxy type and instances
    Core.v      - Category operations and laws
    Prelude.v   - Standard library functions
    Extras.v    - Additional utilities
    Lift.v      - Monad transformer lifting
```

## Important Notes

- The project prefix is `P`, so imports use `Require Import P.Pipes.Core` etc.
- 43 laws have been proven, with 7 requiring the fuel-based compromise (marked in README)
- The codebase closely mirrors Haskell's pipes library but adapted for Coq's requirements