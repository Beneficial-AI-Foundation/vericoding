function factorial(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * factorial(n - 1)
}
function special_factorial_rec(n: nat): nat
  decreases n
{
  if n == 0 then 1 else factorial(n) * special_factorial_rec(n - 1)
}

// <vc-helpers>
lemma lemma_special_factorial_rec_expand(n: nat)
  requires n > 0
  ensures special_factorial_rec(n) == factorial(n) * special_factorial_rec(n - 1)
{
  // This lemma is directly provable from the definition of special_factorial_rec
}

lemma lemma_special_factorial_rec_base_case()
  ensures special_factorial_rec(0) == 1
{
  // This lemma is directly provable from the definition of special_factorial_rec
}
// </vc-helpers>

// <vc-spec>
method special_factorial(n: nat) returns (result: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result == special_factorial_rec(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    result := factorial(1);
    assert factorial(1) == 1; // from definition
    assert special_factorial_rec(1) == factorial(1) * special_factorial_rec(0); // lemma_special_factorial_rec_expand(1)
    assert special_factorial_rec(0) == 1; // lemma_special_factorial_rec_base_case
    assert special_factorial_rec(1) == factorial(1) * 1;
    assert result == special_factorial_rec(1);
  } else {
    var rec_result := special_factorial(n - 1);
    result := factorial(n) * rec_result;
    // Prove postcondition
    // special_factorial_rec(n) == factorial(n) * special_factorial_rec(n - 1) by lemma_special_factorial_rec_expand(n)
    // rec_result == special_factorial_rec(n - 1) by postcondition of recursive call
    // So result == factorial(n) * special_factorial_rec(n - 1) == special_factorial_rec(n)
  }
}
// </vc-code>

