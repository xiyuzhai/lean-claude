import Semantics.Parser
import Semantics.Elaborator
import Semantics.Typeck

/-!
# Semantics Module

This module contains the semantic analysis components for the Lean parser implementation.
The semantics module is organized into three main components:

- Parser: Semantic analysis during parsing
- Elaborator: Type elaboration and inference
- Typeck: Type checking and validation
-/