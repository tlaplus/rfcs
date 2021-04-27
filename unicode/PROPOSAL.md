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

Most mathematical symbols in TLA+ have obvious direct counterparts in unicode.
A few required design decisions:
 1. Most arrow operators (`<-`, `->`, `|->`, etc.) have unicode equivalents of various length; the longest length was chosen as it best matches the displayed width of the ASCII symbol.
 2. In ASCII TLA+, `<=>` and `\equiv` refer to the same operator which is pretty-printed as `≡`; unicode TLA+ proposes to map `<=>` to `⟺` and `\equiv` to `≡`, although semantically they remain the same operator.
 3. The ASCII TLA+ plus-arrow operator `-+->` as pretty-printed has no real unicode equivalent; the symbol `⇸` was chosen as it best resembles the ASCII symbol itself, although other options are available such as `⥅` (closest to pretty-printed version) and `⍆`.
 4. Some ASCII TLA+ operators such as `..`, `...`, `||`, `??`, `!!`, `:=`, and `::=` arguably don't benefit much from translation into their unicode forms, which directly resemble a contraction of their constituent ASCII symbols into a single code point.
 Their translations have been included in the proposal but suggestions on this topic are welcome.
 5. The `\bullet` operator translates to the unicode black circle (U+25CF) symbol `●` instead of the unicode bullet (U+2022) symbol `•` to avoid visual collision with the `\cdot` unicode symbol (U+00B7) `·`.
 6. Some operators such as `\AA`, `\EE`, `\^*`, and `^#` have no clear unicode translation.
