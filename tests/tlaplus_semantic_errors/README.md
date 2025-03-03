This is a large set of TLA⁺ files where each file ending in `Test.tla` should produce a parse error in a standards-conformant TLA⁺ parser.
In addition to simply rejecting the spec, for further standards compliance the parser can output a *standardized error code* in accordance with [RFC15](https://github.com/tlaplus/rfcs/issues/15) that is identified as part of the test case filename.
This error code can then be referenced by users seeking help fixing their error, either from documentation or asking the community.
At this time a list of standardized error codes has been proposed but is not concrete; nor does any corresponding documentation exist.
Thus it suffices to simply check that a given TLA⁺ parser rejects all of these specs.
Currently, the following projects have adapted these tests:
1. [SANY](https://github.com/tlaplus/tlaplus/tree/master/tlatools/org.lamport.tlatools/src/tla2sany)

