---
id: functions
title: Functions (WIP)
keywords:
  - docs
  - reference
  - pikelet
---

A function is a way of relating an input to an output.

## Types

Function types are written as `A -> B`.
Functions are [_curried_][currying-wikipedia], meaning that they take a single input, and return a single output.
Multi-input functions can be created by creating functions that output other functions.

For example, the function type for adding two 32-bit signed integers together is:

```pikelet
S32 -> S32 -> S32
```

### Dependency

Functions output types can also depend on their inputs.
For example this is the type of the identity function:

```pikelet
Fun (A : Type) -> A -> A
```

:::note
These are sometimes called _pi types_ or [_dependent product types_][dependent-product-types-nlab]
in type theory.
:::

### Universes

Function types are also types:

```pikelet
U32 -> U32 : Type
```

In order to find the universe level of a function type,
we use the universe level the largest input or output:

```pikelet
U32 -> Type^2 : Type^3
```

## Terms

Functions are constructed by specifying a list of one-or-more input names after a `fun` token,
and then a output term after a `=>` token.
The inputs can then be referred to in the output term of the function.

```pikelet
fun input-1 input-2 => output
```

Note that functions must always be constructed in a position where they can find a type annotation.
For example, the following function is ambiguous:

```pikelet
fun x y => x
```

The following function passes the type checker,
because the function type is pulled from the record annotation:

```pikelet
record {
    const = fun x y => x,
} : Record {
    const : S32 -> String -> S32,
}
```

:::note
These are sometimes called [_lambda abstractions_][lambda-abstraction-nlab] in type theory,
ore _anonymous functions_ in programming languages.
:::

## Eliminations

Functions can be applied to arguments via [_juxtaposition_][juxtaposition-wikipedia].

For example, this is how the identity function might be applied:

```pikelet
id String "hello!"
```

```pikelet
Array 3 String
```

### Computation

:::note
This section is a work in progress.
:::

(describe beta-reduction)

[currying-wikipedia]: https://en.wikipedia.org/wiki/Currying
[dependent-product-types-nlab]: https://ncatlab.org/nlab/show/dependent+product+type
[lambda-abstraction-nlab]: https://ncatlab.org/nlab/show/lambda-abstraction
[juxtaposition-wikipedia]: https://en.wikipedia.org/wiki/Juxtaposition#Mathematics
