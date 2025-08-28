function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
lemma DivisionExists(k: int)
  requires k >= 2
  ensures (exists j :: 2 <= j < k && k % j == 0) || (forall i :: 2 <= i < k ==> k % i != 0)
{
  // This lemma establishes that for any k >= 2, either there exists a divisor or there doesn't
}

lemma PrimeDefinition(k: int, j: int)
  requires k >= 2 && 2 <= j < k
  requires k % j == 0
  ensures exists w :: 2 <= w < k && k % w == 0
{
  // If we found a divisor j, then j serves as our witness
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
      PrimeDefinition(k, i);
      return false;
    }
    i := i + 1;
  }
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