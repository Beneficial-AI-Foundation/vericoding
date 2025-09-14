// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate HasDivisorInRange(k: int, limit: int) {
  exists i :: 2 <= i < limit && k % i == 0
}
// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)

  requires k >= 2

  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
// </vc-spec>
// <vc-code>
{
  var i := 2;
  while i < k
    invariant 2 <= i <= k
    invariant !HasDivisorInRange(k, i)
  {
    if k % i == 0 {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
