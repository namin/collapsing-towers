# Collapsing Towers of Interpreters

We are concerned with the following challenge: given a sequence of programming 
languages `L_0,...,L_n` and interpreters for `L_i+1` written in `L_i`, derive 
a compiler from `L_n` to `L_0`. This compiler should be one-pass, and it should be
optimal in the sense that the translation removes all interpretive overhead of the
intermediate languages.
