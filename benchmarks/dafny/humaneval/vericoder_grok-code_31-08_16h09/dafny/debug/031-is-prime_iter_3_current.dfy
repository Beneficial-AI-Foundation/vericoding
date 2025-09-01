

// <vc-helpers>
//
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
result := true;
  var i := 2;
  while i < k
    invariant 2 <= i <= k
    invariant result ==> forall x :: 2 <= x < i ==> k % x != 0
    invariant !result ==> exists y :: 2 <= y < i && k % y == 0
  {
    if k % i == 0 {
      result := false;
    }
    i := i + 1;
  }
// </vc-code>

