function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
lemma is_prime_correctness(k: int)
  ensures k >= 2 ==> (is_prime_pred(k) <==> forall i :: 2 <= i < k ==> k % i != 0)
{
  // This lemma establishes the correctness of is_prime_pred
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method is_prime(k: int) returns (result: bool)
Check if condition holds. Requires: the result is at least the specified value. Ensures: the condition holds for all values; there exists a value satisfying the condition.
*/
// </vc-description>

// <vc-spec>
method is_prime(k: int) returns (result: bool)
  requires k >= 2
  ensures result <==> is_prime_pred(k)
  ensures result <==> forall i :: 2 <= i < k ==> k % i != 0
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 2;
  
  while i < k
    invariant 2 <= i <= k
    invariant result <==> forall j :: 2 <= j < i ==> k % j != 0
  {
    if k % i == 0 {
      result := false;
      return;
    }
    i := i + 1;
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