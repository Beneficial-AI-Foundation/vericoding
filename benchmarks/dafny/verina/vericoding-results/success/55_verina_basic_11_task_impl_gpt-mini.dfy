// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsDigit(d: nat) { d < 10 }
// </vc-helpers>

// <vc-spec>
function last_digit(n: nat): nat
// </vc-spec>
// <vc-code>
{
  n % 10
}

lemma last_digit_correct(n: nat)
    ensures
        last_digit(n) < 10
    ensures
        last_digit(n) == n % 10
{
  // unfold definition
  assert last_digit(n) == n % 10;
  // remainder is strictly less than the modulus when modulus > 0
  assert 10 > 0;
  assert n % 10 < 10;
}
// </vc-code>
