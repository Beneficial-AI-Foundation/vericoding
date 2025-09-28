// <vc-preamble>
function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>

function IsComposite(n: nat): bool
  requires n > 1
{
  exists k :: 2 <= k < n && n % k == 0
}

lemma PrimeOrComposite(n: nat)
  requires n > 1
  ensures IsPrime(n) || IsComposite(n)
{
}

// </vc-helpers>

// <vc-spec>
method x_or_y(n: nat, x: int, y: int) returns (result: int)

  ensures IsPrime(n) ==> result == x
  ensures !IsPrime(n) ==> result == y
// </vc-spec>
// <vc-code>
{
  if n <= 1 {
    result := y;
  } else {
    if IsPrime(n) {
      result := x;
    } else {
      result := y;
    }
  }
}
// </vc-code>
