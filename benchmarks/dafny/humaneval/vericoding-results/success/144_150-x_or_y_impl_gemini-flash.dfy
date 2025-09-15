// <vc-preamble>
function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no changes needed */
// </vc-helpers>

// <vc-spec>
method x_or_y(n: nat, x: int, y: int) returns (result: int)

  ensures IsPrime(n) ==> result == x
  ensures !IsPrime(n) ==> result == y
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed compilation by adding braces for if-then-else */
{
  if IsPrime(n) {
    result := x;
  } else {
    result := y;
  }
}
// </vc-code>
