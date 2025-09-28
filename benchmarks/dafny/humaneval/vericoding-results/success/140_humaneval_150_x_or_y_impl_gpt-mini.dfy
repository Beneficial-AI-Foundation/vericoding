// <vc-preamble>
function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
function DecidePrime(n: nat) : bool { IsPrime(n) }
// </vc-helpers>

// <vc-spec>
method x_or_y(n: nat, x: int, y: int) returns (result: int)

  ensures IsPrime(n) ==> result == x
  ensures !IsPrime(n) ==> result == y
// </vc-spec>
// <vc-code>
{
  if DecidePrime(n) {
    result := x;
  } else {
    result := y;
  }
}
// </vc-code>
