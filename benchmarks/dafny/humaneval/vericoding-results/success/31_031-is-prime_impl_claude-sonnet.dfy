// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed decreases clauses to use k - limit for proper termination */
function has_divisor(k: int, limit: int): bool
  requires k >= 2 && limit >= 2
  decreases k - limit
{
  if limit >= k then false
  else if k % limit == 0 then true
  else has_divisor(k, limit + 1)
}

lemma has_divisor_correctness(k: int, limit: int)
  requires k >= 2 && limit >= 2
  ensures has_divisor(k, limit) <==> exists j :: limit <= j < k && k % j == 0
  decreases k - limit
{
  if limit >= k {
    assert !has_divisor(k, limit);
    assert !(exists j :: limit <= j < k && k % j == 0);
  } else if k % limit == 0 {
    assert has_divisor(k, limit);
    assert exists j :: limit <= j < k && k % j == 0;
  } else {
    has_divisor_correctness(k, limit + 1);
    assert has_divisor(k, limit) == has_divisor(k, limit + 1);
    assert (exists j :: limit <= j < k && k % j == 0) <==> (exists j :: limit + 1 <= j < k && k % j == 0);
  }
}
// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)

  requires k >= 2

  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Using helper functions to check primality */
{
  result := !has_divisor(k, 2);
  has_divisor_correctness(k, 2);
}
// </vc-code>
