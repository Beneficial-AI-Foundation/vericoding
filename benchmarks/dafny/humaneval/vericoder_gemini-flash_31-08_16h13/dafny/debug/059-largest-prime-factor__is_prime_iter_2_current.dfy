function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
function is_prime_test(k: int) : bool
{
  if k < 2 then false
  else forall i :: 2 <= i < k ==> k % i != 0
}
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
  if k < 2 {
    result := false;
  } else {
    var i := 2;
    result := true;
    while i * i <= k
      invariant 2 <= i <= k + 1
      invariant result ==> (forall j :: 2 <= j < i ==> k % j != 0)
    {
      if k % i == 0 {
        result := false;
        return;
      }
      i := i + 1;
    }
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