// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPrime (m : int) returns (isPrime : bool)
    requires m > 0
    ensures isPrime <==> (m > 1 && forall j : int :: 2 <= j < m ==> m % j != 0)
// </vc-spec>
// <vc-code>
{
  if m <= 1 {
    isPrime := false;
    return;
  }
  var j := 2;
  while j < m
    invariant 2 <= j <= m
    invariant forall k: int :: 2 <= k < j ==> m % k != 0
  {
    if m % j == 0 {
      isPrime := false;
      return;
    }
    j := j + 1;
  }
  isPrime := true;
}
// </vc-code>
