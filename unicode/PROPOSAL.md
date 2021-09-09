# TLA+ Unicode Translation Proposal

## Motivation

TLA+ specifications can be translated into a "pretty-printed" form with LaTeX, but this is not how developers experience them when writing a spec.
Within the past decade, UTF-8 has become so widely supported that any program limited to ASCII can be seen as deficient.
Supporting unicode in TLA+ provides two main benefits:
 1. Greater inclusivity of cultures where English is not the dominant language
 2. Improved readability while writing a spec

These benefits are facilitated by:
 1. Allowing non-ASCII characters in names & identifiers
 2. Converting mathematical operators into their unicode equivalents on the fly

## Symbol Translation Decisions

The proposed mappings between ASCII and Unicode symbols are found in the `tla-unicode.csv` file in this directory.
There are a number of cases where multiple ASCII symbols map to the same Unicode symbol, for example `<=`, `=<`, and `\leq` all mapping to `≤`.
In these cases the translation from ASCII to Unicode is unambiguous, but the translation back is not.
Thus each ASCII symbol is given a `priority`, where the symbol with the lowest numerical `priority` value is the one chosen when translating from Unicode back to ASCII.
In the `≤` case, `<=` is given priority.

Most mathematical symbols in TLA+ have obvious direct counterparts in unicode.
A few required design decisions:
 1. Most arrow operators (`<-`, `->`, `|->`, etc.) have unicode equivalents of various length; the longest length was chosen as it best matches the displayed width of the ASCII symbol.
 2. In ASCII TLA+, `<=>` and `\equiv` refer to the same operator which is pretty-printed as `≡`; unicode TLA+ proposes to map `<=>` to `⟺` and `\equiv` to `≡`, although semantically they remain the same operator.
 3. The ASCII TLA+ plus-arrow operator `-+->` as pretty-printed has no real unicode equivalent; the symbol `⇸` was chosen as it best resembles the ASCII symbol itself, although other options are available such as `⥅` (closest to pretty-printed version) and `⍆`.
 4. Some ASCII TLA+ operators such as `..`, `...`, `||`, `??`, `!!`, `:=`, and `::=` arguably don't benefit much from translation into their unicode forms, which directly resemble a contraction of their constituent ASCII symbols into a single code point.
 Their translations have been included in the proposal but suggestions on this topic are welcome.
 5. The `\bullet` operator translates to the unicode black circle (U+25CF) symbol `●` instead of the unicode bullet (U+2022) symbol `•` to avoid visual collision with the `\cdot` unicode symbol (U+00B7) `·`.
 6. Some operators such as `\AA`, `\EE`, `\^*`, and `^#` have no clear unicode translation.
 
 ## Drawbacks

Mixing in unicode is not without its drawbacks.

First, conjunction & disjunction lists are a very important part of TLA+ that depend upon vertical alignment.
There are two issues with this: one, rewriting ASCII symbols into their unicode equivalents (for example, `\forall` into `∀`) changes the vertical alignment of everything after them in the line.
So rewriting this:
```tla
op == \forall n \in Nat : /\ n > 0
                          /\ \E o \in Nat : o > n
```
to this:
```tla
op == ∀ n \in Nat : /\ n > 0
                          /\ \E o \in Nat : o > n
```
changes its syntactic structure (although thankfully not, in this case, its semantic meaning).
Thus any TLA+ unicode rewriting utility will have to ensure it does not modify the syntactic structure of conjunction & disjunction lists, requiring potentially complex logic.

Second, still regarding conjunction & disjunction lists - many commonly-used monospace fonts do not render unicode symbols in monospace.
So this:
```tla
op == f ⩴ /\ A
          /\ B
```
will be interpreted by any reasonable parser as a conjunction list, because the number of symbols preceding the `/\` on each line is the same even though their displayed vertical alignment is different.
In contrast, this:
```tla
op == f ⩴ /\ A
           /\ B
```
will *not* be interpreted by any reasonable parser as a conjunction list, because the number of symbols preceding the `/\` on each line is different, even though their displayed vertical alignment is the same.
There exist fonts which render many unicode symbols in monospace, but they are not widely used.
Users might address this issue by adopting the convention of starting conjunction & disjunction lists on a new line, as in:
```tla
op ==
  f ⩴
    /\ A
    /\ B
```
The final issue has to do with ease of learning TLA+.
One difficulty commonly reported by students of TLA+ is that many learning materials are presented in the "pretty printed" form, while they are trying to learn how to write TLA+ the ASCII form.
Since it is difficult to directly type unicode symbols, ASCII TLA+ is likely to remain the dominant input form far into the future.
If unicode TLA+ becomes popular, many example specs will not be in a form which is easily copied by TLA+ newcomers.
This could make the language more difficult to learn.
