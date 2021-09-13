# TLA+ Unicode Translation Proposal

## Motivation

TLA+ specifications can be translated into a "pretty-printed" form with LaTeX, but this is not how developers experience them when writing a spec.
Within the past decade, UTF-8 has become so widely supported that any program limited to ASCII can be seen as deficient.
Supporting Unicode in TLA+ provides two main benefits:
 1. Greater inclusivity of cultures where English is not the dominant language
 2. Improved readability while writing a spec

These benefits are facilitated by:
 1. Allowing non-ASCII characters in names & identifiers
 2. Converting mathematical operators into their Unicode equivalents on the fly

## Symbol Translation Decisions

The proposed mappings between ASCII and Unicode symbols are found in the `tla-unicode.csv` file in this directory.
The file is intended to be both human- and machine-readable to better facilitate creation of translation tools.
There are a number of cases where multiple ASCII symbols map to the same Unicode symbol, for example `<=`, `=<`, and `\leq` all mapping to `≤`.
In these cases the translation from ASCII to Unicode is unambiguous, but the translation back is not.
Each ASCII symbol is listed in a semicolon-separated list where the first element is the one to use when translating back to ASCII.
In the `≤` case, `<=` is given priority - although this (and other cases) can be opened for debate.

Most mathematical symbols in TLA+ have obvious direct counterparts in Unicode.
A few required design decisions:
 1. Most arrow operators (`<-`, `->`, `|->`, etc.) have Unicode equivalents of various length; the shortest length was chosen since more monospace Unicode fonts exist which support them.
 1. There are two sets of angle bracket symbols: `⟨` (U+27E8) and `⟩` (U+27E9), and `〈` (U+3008) and `〉` (U+3009).
 The former were chosen as they lack extraneous space and more monospace Unicode fonts are likely to support them.
 1. There are a number of square symbols available: `□` (U+25A1), `◻` (U+25FB), and `⬜` (U+2B1C).
 In TLA+, the square `[]` is used both as the temporal "always" operator and as a separator in `CASE` statements.
 The small square was chosen for both.
 1. The temporal "leads to" operator `~>` could be translated to either `↝` (U+2198) or `⇝` (U+21DD).
 The latter was chosen as it is more visually distinctive.
 1. In ASCII TLA+, `<=>` and `\equiv` refer to the same operator which is pretty-printed as `≡`; Unicode TLA+ proposes to map `<=>` to `⇔` and `\equiv` to `≡`, although semantically they remain the same operator.
 1. The ASCII TLA+ plus-arrow operator `-+->` as pretty-printed has no real Unicode equivalent; the symbol `⇸` was chosen as it best resembles the ASCII symbol itself, although other options are available such as `⥅` (closest to pretty-printed version) and `⍆`.
 1. Some ASCII TLA+ operators such as `..`, `...`, `||`, `??`, `!!`, `:=`, and `::=` arguably don't benefit much from translation into their Unicode forms, which directly resemble a contraction of their constituent ASCII symbols into a single code point.
 Their translations have been included in the proposal but suggestions on this topic are welcome.
 1. The `\bullet` operator translates to the Unicode black circle (U+25CF) symbol `●` instead of the Unicode bullet (U+2022) symbol `•` to avoid visual collision with the `\cdot` Unicode symbol (U+00B7) `·`.
 1. Some operators such as `\AA`, `\EE`, `\^*`, and `^#` have no clear Unicode translation.
 
 ## Challenges

Mixing in Unicode is not without its challenges.

First, conjunction & disjunction lists are a very important part of TLA+ that depend upon vertical alignment.
One issue with this is that rewriting ASCII symbols into their Unicode equivalents (for example, `\forall` into `∀`) changes the vertical alignment of everything after them in the line.
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
Thus any TLA+ Unicode rewriting utility will have to ensure it does not modify the syntactic structure of conjunction & disjunction lists, requiring potentially complex logic.

Second, still regarding conjunction & disjunction lists - many commonly-used monospace fonts do not render Unicode symbols in monospace.
So this:
```tla
op == f ⩴ /\ A
          /\ B
```
will be interpreted by any reasonable parser as a conjunction list, because the number of symbols preceding the `/\` on each line is the same even though their displayed vertical alignment is different (depending on the font used to render this document).
In contrast, this:
```tla
op == f ⩴ /\ A
           /\ B
```
will *not* be interpreted by any reasonable parser as a conjunction list, because the number of symbols preceding the `/\` on each line is different, even though their displayed vertical alignment is the same (again, depending on the font used to render this document).
There exist fonts which render many Unicode symbols in monospace, but they are not widely used.
Users might address this issue by adopting the convention of starting conjunction & disjunction lists on a new line, as in:
```tla
op ==
  f ⩴
    /\ A
    /\ B
```
The final issue has to do with ease of learning TLA+.
One difficulty commonly reported by students of TLA+ is that many learning materials are presented in the "pretty printed" form, while they are trying to learn how to write TLA+ in the ASCII form.
Since it is difficult to directly type Unicode symbols, ASCII TLA+ is likely to remain the dominant input form far into the future.
If Unicode TLA+ becomes popular, many example specs will not be in a form which is easily copied by TLA+ newcomers.
This could make the language more difficult to learn.

## Prior Art

In 2017 Ron Pressler created a set of changes intended to add Unicode support to SANY; this work can be viewed [here](https://github.com/pron/tlaplus/tree/unicode-presentation-2/tlatools/src/tla2unicode).
This was at one point integrated into a beta toolbox release (along with real-time rewriting of ASCII symbols into their Unicode counterparts!) but was reverted after it caused various issues; see release announcement discussion [here](https://groups.google.com/g/tlaplus/c/YEWzqRqV8Nc/m/mKhyim0wCQAJ) and prior general discussion of Unicode in TLA+ [here](https://groups.google.com/g/tlaplus/c/9ZKemfayRDk/m/Ii5ugPtHIAAJ).


