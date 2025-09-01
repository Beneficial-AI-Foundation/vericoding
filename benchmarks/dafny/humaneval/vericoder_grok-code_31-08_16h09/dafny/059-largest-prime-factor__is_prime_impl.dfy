function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
// </vc-helpers>
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
  result := true;
  var i := 2;
  while i < k
    invariant 2 <= i <= k
    invariant result ==> forall j :: 2 <= j < i ==> k % j != 0
    invariant !result ==> exists j :: 2 <= j < i && k % j == 0
    decreases k - i
  {
    if k % i == 0 {
      result := false;
      assert 2 <= i < k && k % i == 0;
      break;
    }
    i := i + 1;
  }
  if result {
    assert i == k;
  }
  assert result ==> forall j :: 2 <= j < k ==> k % j != 0;
}
// </vc-code>

method largest_prime_factor(n: int) returns (largest: int)
  // pre-conditions-start
  requires n >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
  // post-conditions-end
{
  assume{:axiom} false;
}