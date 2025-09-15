// <vc-preamble>
function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
function ChooseResult(n: nat, x: int, y: int): int { if IsPrime(n) then x else y }
// </vc-helpers>

// <vc-spec>
method x_or_y(n: nat, x: int, y: int) returns (result: int)

  ensures IsPrime(n) ==> result == x
  ensures !IsPrime(n) ==> result == y
// </vc-spec>
// <vc-code>
{
  if IsPrime(n) {
    result := x;
  } else {
    result := y;
  }
}
// </vc-code>
