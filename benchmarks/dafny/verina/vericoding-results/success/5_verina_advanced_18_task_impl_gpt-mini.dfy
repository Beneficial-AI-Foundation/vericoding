// <vc-preamble>
function CountDigits(n: nat): nat
    decreases n
{
    if n == 0 then 1 else if n < 10 then 1 else 1 + CountDigits(n / 10)
}

function PowNat(base: nat, exp: nat): nat
    decreases exp
{
    if exp == 0 then 
        1 
    else 
        base * PowNat(base, exp - 1)
}

function SumPowers(n: nat, k: nat): nat
    decreases n
{
    if n == 0 then 0 else PowNat(n % 10, k) + SumPowers(n / 10, k)
}
// </vc-preamble>

// <vc-helpers>
lemma CountDigitsAtLeastOne(n: nat)
  ensures CountDigits(n) >= 1
  decreases n
{
  if n == 0 {
    assert CountDigits(0) == 1;
  } else if n < 10 {
    assert CountDigits(n) == 1;
  } else {
    CountDigitsAtLeastOne(n / 10);
    assert CountDigits(n) == 1 + CountDigits(n / 10);
    assert CountDigits(n / 10) >= 1;
    assert CountDigits(n) >= 2;
  }
}
// </vc-helpers>

// <vc-spec>
method IsArmstrong(n: nat) returns (result: bool)
    ensures 
        result == (n == SumPowers(n, CountDigits(n)))
// </vc-spec>
// <vc-code>
{
  var k := CountDigits(n);
  var s := SumPowers(n, k);
  result := n == s;
}
// </vc-code>
