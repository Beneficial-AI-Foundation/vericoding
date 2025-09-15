// <vc-preamble>
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Remove duplicate function and add lemma for prime property */
lemma is_prime_pred_lemma(k: int)
  requires k >= 2
  ensures is_prime_pred(k) == (forall i :: 2 <= i < k ==> k % i != 0)
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
/* code modified by LLM (iteration 2): Use lemma to connect predicate with method logic */
{
  is_prime_pred_lemma(k);
  result := is_prime_pred(k);
  if !result {
    var j :| 2 <= j < k && k % j == 0;
  }
}
// </vc-code>
