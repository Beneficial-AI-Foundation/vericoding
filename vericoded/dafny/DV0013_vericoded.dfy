// <vc-preamble>
function Power(base: int, exp: nat): int
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Simplified helpers with direct equivalence proof */
function IsPowerOfFourComputable(n: nat): bool
{
  if n == 0 then false
  else if n == 1 then true
  else if n % 4 != 0 then false
  else IsPowerOfFourComputable(n / 4)
}

lemma PowerPositive(m: nat)
  ensures Power(4, m) >= 1
{
  if m == 0 {
    assert Power(4, 0) == 1;
  } else {
    PowerPositive(m - 1);
    assert Power(4, m) == 4 * Power(4, m - 1);
    assert Power(4, m - 1) >= 1;
    assert Power(4, m) >= 4;
  }
}

lemma IsPowerOfFourCorrect(n: nat)
  ensures IsPowerOfFourComputable(n) <==> (exists m: nat :: n == Power(4, m))
{
  if n == 0 {
    if exists m: nat :: n == Power(4, m) {
      var m: nat :| n == Power(4, m);
      PowerPositive(m);
      assert Power(4, m) >= 1;
      assert false;
    }
  } else if n == 1 {
    assert n == Power(4, 0);
    assert exists m: nat :: n == Power(4, m);
  } else if n % 4 != 0 {
    if exists m: nat :: n == Power(4, m) {
      var m: nat :| n == Power(4, m);
      if m == 0 {
        assert n == 1;
        assert false;
      } else {
        assert n == 4 * Power(4, m - 1);
        assert n % 4 == 0;
        assert false;
      }
    }
  } else {
    IsPowerOfFourCorrect(n / 4);
    if exists m: nat :: n == Power(4, m) {
      var m: nat :| n == Power(4, m);
      assert m > 0;
      assert n / 4 == Power(4, m - 1);
      assert exists k: nat :: n / 4 == Power(4, k);
    }
    if exists m: nat :: n / 4 == Power(4, m) {
      var m: nat :| n / 4 == Power(4, m);
      assert n == Power(4, m + 1);
      assert exists k: nat :: n == Power(4, k);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method IfPowerOfFour(n: nat) returns (result: bool)
    ensures result <==> (exists m: nat :: n == Power(4, m))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Direct call to lemma that establishes postcondition */
{
  result := IsPowerOfFourComputable(n);
  IsPowerOfFourCorrect(n);
}
// </vc-code>
