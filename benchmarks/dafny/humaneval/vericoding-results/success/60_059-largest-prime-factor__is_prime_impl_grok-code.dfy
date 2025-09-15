// <vc-preamble>
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)

  requires k >= 2

  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Modified loop to check up to k/2 instead of sqrt(k) to eliminate need for lemma and avoid verification timeout. */
{
  result := true;
  var i := 2;
  while i <= k / 2
    invariant 2 <= i
    invariant forall j :: 2 <= j < i ==> k % j != 0
  {
    if k % i == 0 {
      result := false;
      break;
    }
    i := i + 1;
  }
}
// </vc-code>
