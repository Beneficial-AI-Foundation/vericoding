// <vc-preamble>
function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PrimeLength(s: string) returns (p : bool)

  ensures p <==> IsPrime(|s|)
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  if n <= 1 {
    p := false;
  } else {
    var k := 2;
    while k < n
      invariant 2 <= k <= n
      invariant forall j :: 2 <= j < k ==> n % j != 0
    {
      if n % k == 0 {
        p := false;
        return;
      }
      k := k + 1;
    }
    p := true;
  }
}
// </vc-code>
