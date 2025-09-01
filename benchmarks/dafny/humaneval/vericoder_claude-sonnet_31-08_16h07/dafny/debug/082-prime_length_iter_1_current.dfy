function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PrimeLength(s: string) returns (p : bool)
  // post-conditions-start
  ensures p <==> IsPrime(|s|)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var length := |s|;
  if length <= 1 {
    p := false;
  } else {
    p := true;
    var k := 2;
    while k < length
      invariant 2 <= k <= length
      invariant p <==> (forall j :: 2 <= j < k ==> length % j != 0)
    {
      if length % k == 0 {
        p := false;
      }
      k := k + 1;
    }
  }
}
// </vc-code>

