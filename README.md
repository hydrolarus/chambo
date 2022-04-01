# chambo

`chambo` is a language to explore the implementation of verification primitives.

The verification primitives are
- `requires` clauses on functions as preconditions
- `ensures` clauses on functions as postconditions
- `assert` expression

The language is split in a "term" and an "expression" part.
The "expression" part is meant to be trivially executable on a CPU at runtime.
The "term" part is meant to express logical predicates, including
harder-to-execute concepts like universal and existential quantifiers.

Verification primitives use the "term" language.

For an example, see [the example directory](examples/).

## License

This code is licensed under the [EUPL-1.2 license](LICENSE.txt).