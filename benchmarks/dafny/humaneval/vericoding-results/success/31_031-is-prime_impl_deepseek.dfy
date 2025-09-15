// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function HasFactor(k: int, j: int): bool requires k >= 2 && j >= 2 { k % j == 0 }

predicate FactorsInRange(k: int, n: int) requires k >= 2 && n >= 2 { exists j :: n <= j < k && HasFactor(k, j) }

lemma FactorsLemma(k: int, n: int) 
  requires k >= 2 && n >= 2
  ensures FactorsInRange(k, n) == (exists j :: n <= j < k && HasFactor(k, j)) 
{
}

lemma NoFactorsLemma(k: int, n: int)
  requires k >= 2 && n >= 2
  ensures (forall i :: n <= i < k ==> !HasFactor(k, i)) == !FactorsInRange(k, n)
{
}
// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)

  requires k >= 2

  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added proper verification for prime check */
  if (k == 2) {
    result := true;
  } else {
    var i := 2;
    result := true;
    while (i < k)
      invariant 2 <= i <= k
      invariant result ==> (forall j :: 2 <= j < i ==> k % j != 0)
    {
      if (k % i == 0) {
        result := false;
        return;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
