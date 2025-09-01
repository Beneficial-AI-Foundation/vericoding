function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

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
  var w: int := 0;
  while i < k && !found
    invariant 2 <= i <= k
    invariant !found ==> (forall j :: 2 <= j < i ==> k % j != 0)
    invariant found ==> (2 <= w < k && k % w == 0)
    decreases k - i + (if found then 0 else 1)
  {
    if k % i == 0 {
      found := true;
      w := i;
    } else {
      i := i + 1;
    }
  }
  if found {
    result := false;
  } else {
    result := true;
  }
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