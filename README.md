# Introduction to Dafny

Short introduction to Dafny as a vehicle for proofs, as well as a reference for
Dafny syntax. Focuses on mathematical objects, so no executable functions,
loops, or heap reasoning.

If you'd prefer a video version, we have a [series of YouTube
lectures](https://www.youtube.com/playlist?list=PLGRomBFFLGeou_T_ce3nfRagJarH21lim)
based on this code. The comments in the Dafny files are intended to be
standalone if you prefer text (or if you want to reference something).

## Outline

[Lecture 1 (logic)](src/lec1_logic.dfy): lemmas, functions, and assertions

[Lecture 2 (sequences)](src/lec2_sequences.dfy): the built-in sequence data type

[Lecture 3 (algebraic datatypes)](src/lec3_algebraic_datatypes.dfy): algebraic
datatypes for user-defined data

[Lecture 4 (advanced topics)](src/lec4_advanced.dfy): an assortment of advanced
topics: opacity/revealing, recursion, and assign-such-that.

----

This tutorial was originally written for a [VMware protocol verification
course](https://github.com/jonhnet/vmware-verification-2023), but we hope it's
useful to others!

The text of this tutorial is licensed under
[CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/). The code is licensed
under the MIT license.
