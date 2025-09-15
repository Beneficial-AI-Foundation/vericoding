// <vc-preamble>
function odd_count(n: nat): nat {
  if n == 0 then 0
  else odd_count(n / 10) + n % 2
}
function even_count(n: nat): nat
{
  if n == 0 then 0
  else even_count(n / 10) + (1 - n % 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed unused helper functions and kept count_digits as it is used in the invariants. */
function count_digits(n: nat): nat
{
  if n == 0 then 0
  else 1 + count_digits(n / 10)
}
// </vc-helpers>

// <vc-spec>
method even_odd_count(n: nat) returns (even: nat, odd: nat)

  requires n > 0

  ensures even == even_count(n)
  ensures odd == odd_count(n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): The previous implementation was not using the loop invariants correctly. This version has been fixed to compute the even and odd counts correctly. The termination errors were due to the recursion in the helper functions not having a decreases clause. However, there were logic errors in the interpretation of these functions. The current approach iterates through the digits of `n` to directly compute `even` and `odd`. This correctly implements the specification and clears the termination and division by zero errors. */
{
  var temp_n := n;
  even := 0;
  odd := 0;

  while temp_n > 0
    decreases temp_n
    invariant even + odd == count_digits(n) - count_digits(temp_n)
    invariant even == even_count(n) - even_count(temp_n)
    invariant odd == odd_count(n) - odd_count(temp_n)
  {
    var digit := temp_n % 10;
    if digit % 2 == 0 {
      even := even + 1;
    } else {
      odd := odd + 1;
    }
    temp_n := temp_n / 10;
  }
}
// </vc-code>
