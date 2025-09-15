// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsDivisor(k: int, d: int) { 2 <= d && d < k && k % d == 0 }
// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)

  requires k >= 2

  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
// </vc-spec>
// <vc-code>
{
  var d := 2;
  var found := false;
  var w := 0;
  while d < k
    invariant 2 <= d <= k
    invariant !found ==> forall i :: 2 <= i < d ==> k % i != 0
    invariant found ==> 2 <= w < d && k % w == 0
    decreases k - d
  {
    if !found && k % d == 0 {
      found := true;
      w := d;
    }
    if !found {
      assert k % d != 0;
    }
    d := d + 1;
  }
  if found {
    result := false;
    assert 2 <= w < k && k % w == 0;
  } else {
    result := true;
  }
}
// </vc-code>
