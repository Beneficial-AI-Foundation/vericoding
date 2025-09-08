/-
Normally, we decompose a number into binary digits by assigning it with powers of 2, with a coefficient of `0` or `1` for each term:

`25 = 1*16 + 1*8 + 0*4 + 0*2 + 1*1`

The choice of `0` and `1` is... not very binary. We shall perform the *true* binary expansion by expanding with powers of 2, but with a coefficient of `1` or `-1` instead:

`25 = 1*16 + 1*8 + 1*4 - 1*2 - 1*1`

Now *this* looks binary.

---

Given any positive number `n`, expand it using the true binary expansion, and return the result as an array, from the most significant digit to the least significant digit.

`true_binary(25) == [1,1,1,-1,-1]`

It should be trivial (the proofs are left as an exercise to the reader) to see that:

- Every odd number has infinitely many true binary expansions
- Every even number has no true binary expansions

Hence, `n` will always be an odd number, and you should return the *least* true binary expansion for any `n`.

Also, note that `n` can be very, very large, so your code should be very efficient.
-/

-- <vc-helpers>
-- </vc-helpers>

def true_binary (n : Nat) : List Int := sorry

theorem true_binary_starts_with_one {n : Nat} (h : n % 2 = 1) :
  match true_binary n with
  | [] => False 
  | x::xs => x = 1
  := sorry

theorem true_binary_elements_are_ones {n : Nat} (h : n % 2 = 1) :
  ∀ x ∈ true_binary n, x = 1 ∨ x = -1 := sorry

theorem true_binary_length {n : Nat} (h : n % 2 = 1) :
  List.length (true_binary n) = Nat.log2 n := sorry

/-
info: [1, 1, 1, -1, -1]
-/
-- #guard_msgs in
-- #eval true_binary 25

/-
info: [1, 1, -1, 1, 1, 1]
-/
-- #guard_msgs in
-- #eval true_binary 47

/-
info: [1]
-/
-- #guard_msgs in
-- #eval true_binary 1

-- Apps difficulty: introductory
-- Assurance level: unguarded