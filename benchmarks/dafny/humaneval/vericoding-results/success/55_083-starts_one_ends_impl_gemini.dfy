// <vc-preamble>
function Pow(base: nat, exponent: nat): nat
    ensures exponent == 0 ==> Pow(base, exponent) == 1
    ensures exponent > 0 ==> Pow(base, exponent) == base * Pow(base, exponent-1)
{
    if exponent == 0 then 1 else base * Pow(base, exponent-1)
}
// </vc-preamble>

// <vc-helpers>
lemma CountFormula(n: nat)
  requires n > 1
  ensures Pow(10, n - 1) + 9 * Pow(10, n - 2) - Pow(10, n - 2) == 18 * Pow(10, n - 2)
{}
// </vc-helpers>

// <vc-spec>
method CountNumbersStartingOrEndingWithOne(n: nat) returns (count: nat)

    requires n > 0

    ensures n == 1 ==> count == 1
    ensures n > 1 ==> count == 18 * Pow(10, n - 2)
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    count := 1;
  } else {
    var count_starts_with_one := Pow(10, n - 1);
    var count_ends_with_one := 9 * Pow(10, n - 2);
    var count_both := Pow(10, n - 2);
    count := count_starts_with_one + count_ends_with_one - count_both;
    CountFormula(n);
  }
}
// </vc-code>
