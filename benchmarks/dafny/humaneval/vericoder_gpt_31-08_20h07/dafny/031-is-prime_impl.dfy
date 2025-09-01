

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
  var found := false;
  var d := 2;
  while i < k && !found
    invariant 2 <= i <= k
    invariant found ==> 2 <= d < k && k % d == 0
    invariant !found ==> forall j :: 2 <= j < i ==> k % j != 0
    decreases k - i
  {
    if k % i == 0 {
      found := true;
      d := i;
    }
    i := i + 1;
  }
  if found {
    result := false;
    assert 2 <= d < k && k % d == 0;
  } else {
    result := true;
    assert i == k;
    assert forall j :: 2 <= j < k ==> k % j != 0 by {
      forall j | 2 <= j < k
        ensures k % j != 0
      {
        assert j < i;
        assert 2 <= j < i;
      }
    }
  }
}
// </vc-code>

