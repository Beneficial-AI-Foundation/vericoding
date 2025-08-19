# BigNum

# CHALLENGE 1:

Implement basic arithmetic for arbitrarily large natural numbers ("bignats") represented as strings
containing only characters "0" and "1".

- We define natural numbers represented as bitstrings (e.g., "1011").
- All operations are purely structural (not using built-in `+`, `-`, `*` in core logic).
- Operations (`BigNum/Defs.lean`):
  - `add`: adds two bignat strings, (*complete with correctness proof*)
  - `sub`: computes the difference between two bignat strings (*definition only*)
  - `mul`: computes the product of two bignat strings (*complete with correctness proof*)
  - `modadd`: addition modulo n, i.e., computes $$a+b \mod n$$ (*to do*)
  - `modmul`: multiplication modulo n, , i.e., computes $$a*b \mod n$$ (*to do*)
  - `modexp`: exponentiation modulo n, i.e., computes $$a^b \mod n$$ (*to do*)
- Remark: mod for a power of two complete with correctness proof, various lemmas ready for general mod.
- Utility functions (`BigNum/Defs.lean`):
  - `strToNat`: converts bignat string to nat (*complete with correctness proof*)
  - `natToStr`: converts nat to bignat string (*complete with correctness proof*)
