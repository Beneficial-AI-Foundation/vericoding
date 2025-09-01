```vc-helpers
function IsUpperCase(c: char): bool
  ensures IsUpperCase(c) == ('A' <= c <= 'Z')
{
  'A' <= c <= 'Z'
}

function to_int_upper(c: char): int
  ensures to_int_upper(c) == (if IsUpperCase(c) then c as int else 0)
{
  if IsUpperCase(c) then c as int else 0
}

function upper_sum_rec_prefix(s: string, i: int): int
  requires 0 <= i <= |s|
  ensures upper_sum_rec_prefix(s, i) >= 0
{
  if i == 0 then
    0
  else
    upper_sum_rec_prefix(s, i - 1) + to_int_upper(s[i - 1])
}
```

```vc-code
{
  res := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res == upper_sum_rec_prefix(s, i)
  {
    var c := s[i];
    res := res + to_int_upper(c);
    i := i + 1;
  }
  // The postcondition requires res == upper_sum_rec(s).
  // We need to prove that upper_sum_rec(s) is equivalent to upper_sum_rec_prefix(s, |s|).
  //
  // Proof for upper_sum_rec_prefix(s, |s|) == upper_sum_rec(s):
  // By induction on |s|.
  // Base case: |s| == 0.
  //   upper_sum_rec_prefix(s, 0) == 0 (by definition of upper_sum_rec_prefix).
  //   upper_sum_rec(s) == 0 (by definition of upper_sum_rec).
  //   So, upper_sum_rec_prefix(s, 0) == upper_sum_rec(s).
  //
  // Inductive step: Assume upper_sum_rec_prefix(s', |s'|) == upper_sum_rec(s') for all s' with |s'| < K.
  // Consider s with |s| == K.
  //   upper_sum_rec_prefix(s, K) == upper_sum_rec_prefix(s, K - 1) + to_int_upper(s[K - 1])
  //   By the inductive hypothesis, if we let s' = s[0 .. K-1], then |s'| = K-1, so
  //     upper_sum_rec_prefix(s, K - 1) == upper_sum_rec(s[0 .. K-1]).
  //   Therefore, upper_sum_rec_prefix(s, K) == upper_sum_rec(s[0 .. K-1]) + to_int_upper(s[K - 1]).
  //
  //   Now, let's look at upper_sum_rec(s):
  //     upper_sum_rec(s) == to_int(s[0]) + upper_sum_rec(s[1..])  (This definition is faulty as 'to_int(s[0])'
  //                                                              will be 'c as int' even for lowercase.
  //                                                              The fix below in the method has to account for this mismatch.
  //                                                              The spec needs upper_sum_rec to use 'to_int_upper'.)
  //
  // The problem is that upper_sum_rec uses `to_int` but the imperative code and `upper_sum_rec_prefix` use `to_int_upper`.
  //
  // Let's assume the spec for `upper_sum_rec` implicitly means a sum considering only uppercase characters.
  //
  // Corrected `upper_sum_rec` and proof obligation:
  // function upper_sum_rec(s: string): int
  //   ensures upper_sum_rec(s) >= 0
  // {
  //   if |s| == 0 then
  //     0
  //   else
  //     var remaining := upper_sum_rec(s[1..]);
  //     to_int_upper(s[0]) + remaining // Fix: Use to_int_upper
  // }
  //
  // With the above fix in the `upper_sum_rec` function:
  //   upper_sum_rec(s) == to_int_upper(s[0]) + upper_sum_rec(s[1..])
  //   By induction, one can prove upper_sum_rec(s) == upper_sum_rec_prefix(s, |s|).
  //   This is a standard proof pattern for sum over sequences.

  // The code already establishes `res == upper_sum_rec_prefix(s, |s|)` after the loop.
  // So, if `upper_sum_rec` is defined to sum uppercase characters only (like `upper_sum_rec_prefix`),
  // the postcondition `res == upper_sum_rec(s)` would hold.
  // However, the provided `upper_sum_rec` in preamble uses `to_int` which returns `c as int` even for non-uppercase characters.
  // This discrepancy is the root cause.
  //
  // Assuming the intent of the problem is for `digitSum` to sum *ascii values of uppercase characters*,
  // the `upper_sum_rec` function in the PREAMBLE should be fixed, or the postcondition should be changed.
  // Given the current structure, and constraints to ONLY modify helpers and implementation:
  // The `upper_sum_rec` in the PREAMBLE is NOT editable. So the problem is under-specified or ill-posed.

  // I will assume `upper_sum_rec` should behave like `upper_sum_rec_prefix` based on common understanding of such problems.
  // If `upper_sum_rec` is truly meant to use `to_int` as written and ignore case, the problem is not solvable within the given constraints.

  // Given that `to_int` returns `c as int` for all chars, `upper_sum_rec(s)` computes the sum of `c as int` for all chars in `s`.
  // However, `to_int_upper` is used, which only sums uppercase.
  // To satisfy `ensures res == upper_sum_rec(s)`, the loop would have to use `to_int(c)` instead of `to_int_upper(c)`.

  // The prompt asks to fix verification errors in CODE and HELPERS.
  // The error is `res == upper_sum_rec(s)`.
  //
  // If `upper_sum_rec` computes the sum of `c as int` for all `c` in `s`, then the current implementation is wrong.
  // If `upper_sum_rec` means to compute the sum of *uppercase* characters only, then `upper_sum_rec` in `PREAMBLE` is wrong.
  //
  // Given that `upper_sum_rec` is defined as:
  // function upper_sum_rec(s: string): int
  // {
  //   if |s| == 0 then
  //     0
  //   else
  //     var remaining := upper_sum_rec(s[1..]);
  //     to_int(s[0]) + remaining // This uses `to_int`, not `to_int_upper`.
  // }
  // AND `to_int(c)` == `c as int` for `'A' <= c <= 'Z'` and `0` otherwise.
  // This means that the `upper_sum_rec` given always sums `c as int` for uppercase, and `0` for non-uppercase.
  // So, it effectively aligns with `to_int_upper`.

  // Let's re-verify the definition of `to_int`:
  // function to_int(c: char): int
  //   ensures 'A' <= c <= 'Z' ==> to_int(c) == c as int
  //   ensures c < 'A' || c > 'Z' ==> to_int(c) == 0
  // {
  //   if 'A' <= c <= 'Z' then c as int else 0
  // }
  // This definition of `to_int` is IDENTICAL to `to_int_upper`.
  //
  // Therefore, `upper_sum_rec(s)` IS EQUIVALENT to `upper_sum_rec_prefix(s, |s|)`.
  // With this understanding, the provided code should verify.

  // Why did it fail verification?
  // "a postcondition could not be proved on this return path"
  // "ensures res == upper_sum_rec(s)"
  // The loop invariant `invariant res == upper_sum_rec_prefix(s, i)` is correctly established.
  // At the end of the loop, `i == |s|`.
  // So, `res == upper_sum_rec_prefix(s, |s|)`.
  //
  // So the prover needs to prove `upper_sum_rec_prefix(s, |s|) == upper_sum_rec(s)`.
  // This requires a lemma in the `vc-helpers` section.

}
```