# Ambiguity

While a lot of cases of ambiguity within the grammer are already covered, there are a few that are only checked at runtime when actually parsed.

## `SelfRepetition`

If any of the non-exhaustive fields of a struct contains a repetition of itself:

```rs
struct SelfRepetition {
    dummy: [Ident],
    // any other fields
    more: (SelfRepetition[*]),
    // any other non-exhaustive (optional/repetition) fields
}
```

Then it is ambiguous in whether push into `more` recursively (think linked list) or only into the top level without any further `more` elements inside.

## `RecursiveRepetition`

It is also possible to run into a similar issue across multiple nodes, including enums:

```rs
struct A {
    dummy: [Integer],
    b: (B[*]),
}

struct B {
    a: (A),
}
```

It doesn't matter whether the reptition is on `A` or `B`:

```rs
struct A2 {
    dummy: [Integer],
    b: (B2),
}

struct B2 {
    a: (A2[*]),
}
```

Adding a dummy before `a` in `B` as well is still ambiguous:

```rs
struct A3 {
    dummy: [Integer],
    b: (B3),
}

struct B3 {
    dummy: [Float],
    a: (A3[*]),
}
```

However, adding a dummy to `B`, but *after* `a` works:

```rs
struct A4 {
    dummy: [Integer],
    b: (B4),
}

struct B4 {
    a: (A4[*]),
    dummy: [Float],
}
```

Since now it is basically the same as:

```rs
struct MatchingParens {
    l_paren: [LParen],
    inner: (MatchingParens*),
    r_paren: [RParen],
}
```

`B` simply got "inlined" into `A`.

## Conclusion

- For all non-exhaustive repetition fields `F` on struct `T` ensure that
  - `F` is not `T` and
  - The last required field `R` of `F` is not `T` and
  - None of the non-exhaustive `N...` fields of `F` is `T` and
  - Recursively check the same thing as for `F` for all `N...`

Note, that for the initial type `T` it is impossible to have `T` as the last required (well, any required) field, since that would introduce an endless unparsable cycle, which is already covered by the fact, that such a type would have infinite size, which Rust cannot compile anyway.
