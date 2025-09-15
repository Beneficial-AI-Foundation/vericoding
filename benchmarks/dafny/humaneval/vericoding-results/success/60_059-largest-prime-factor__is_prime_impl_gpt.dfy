// <vc-preamble>
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate for proper divisors */
predicate ProperDivisor(k: int, d: int) { 2 <= d && d < k && k % d == 0 }
/* helper modified by LLM (iteration 3): predicate stating primality via absence of proper divisors */
predicate NoProperDivisors(k: int) { forall d :: 2 <= d < k ==> k % d != 0 }
/* helper modified by LLM (iteration 3): lemma relating helper predicate to the specification form */
lemma NoProperDivisorsImpliesSpec(k: int)
  ensures NoProperDivisors(k) ==> (forall i :: 2 <= i < k ==> k % i != 0)
{ }
// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)

  requires k >= 2

  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): trial division with explicit witness and safe invariants */
  var i := 2;
  var found := false;
  var div := 2;
  while i < k
    decreases k - i
    invariant 2 <= i && i <= k
    invariant found ==> (2 <= div && div < i && k % div == 0)
    invariant !found ==> (forall j :: 2 <= j && j < i ==> k % j != 0)
  {
    if k % i == 0 {
      found := true;
      div := i;
      i := k;
    } else {
      i := i + 1;
    }
  }
  if found {
    result := false;
    assert 2 <= div && div < k && k % div == 0;
    assert exists j :: 2 <= j < k && k % j == 0;
  } else {
    result := true;
    assert forall j :: 2 <= j < k ==> k % j != 0;
  }
}
// </vc-code>
