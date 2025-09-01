function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
lemma prime_divisibility_lemma(k: int, j: int)
  requires k >= 2 && 2 <= j < k && k % j == 0
  ensures exists i :: 2 <= i < k && k % i == 0
{
}

lemma no_divisor_implies_prime(k: int)
  requires k >= 2
  requires forall i :: 2 <= i < k ==> k % i != 0
  ensures is_prime_pred(k)
{
}

lemma divisor_exists_implies_not_prime(k: int)
  requires k >= 2
  requires exists j :: 2 <= j < k && k % j == 0
  ensures !is_prime_pred(k)
{
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
  var i := 2;
  while i < k
    invariant 2 <= i <= k
    invariant forall j :: 2 <= j < i ==> k % j != 0
  {
    if k % i == 0 {
      prime_divisibility_lemma(k, i);
      return false;
    }
    i := i + 1;
  }
  no_divisor_implies_prime(k);
  return true;
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