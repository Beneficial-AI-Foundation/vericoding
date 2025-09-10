

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 2;
  while i < k
    invariant 2 <= i <= k
    invariant forall t :: 2 <= t < i ==> k % t != 0
    decreases k - i
  {
    if k % i == 0 {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

