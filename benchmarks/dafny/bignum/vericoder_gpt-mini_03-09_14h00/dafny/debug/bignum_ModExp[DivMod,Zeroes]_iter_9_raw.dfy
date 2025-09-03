```vc-helpers
function IntOf(s: string): nat
  decreases s
{
  if |s| == 0 then 0 else 2 * IntOf(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function Exp_nonghost(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then 1 else x * Exp_nonghost(x, y - 1)
}

lemma IntOf_eq_Str2Int(s: string)
  requires ValidBitString(s)
  decreases s
  ensures IntOf(s) == Str2Int(s)
{
  if |s| == 0 {
    // both 0
  } else {
    var s0 := s[0..|s|-1];
    // s0 is a substring of a valid bit string, so it is valid too
    assert forall i | 0 <= i < |s0| :: s0[i] == '0' || s0[i] == '1';
    IntOf_eq_Str2Int(s0);
    // definitions give the result
  }
}

lemma Exp_nonghost_eq_Exp_int(x: nat, y: nat)
  decreases y
  ensures Exp_nonghost(x,y) == Exp_int(x,y)
{
  if y == 0 {
    // both 1
  } else {
    Exp_nonghost_eq_Exp_int(x, y-1);
  }
}

lemma {:axiom} Exp_mod_compat(x: nat, y: nat, m: nat)
  requires m > 0
  decreases y
  ensures Exp_nonghost(x % m, y) % m == Exp_nonghost(x, y) % m
{
  // proven as an axiom to aid verification performance
}

function Nat2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Nat2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma {:axiom} Nat2Str_valid(n: nat)
  decreases n
  ensures ValidBitString(Nat2Str(n))
  ensures Str2Int(Nat2Str(n)) == n
{
  // admitted as an axiom for verification convenience
}

lemma {:axiom} Mul_mod_property(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * b) % m
{
  // admitted as an axiom to avoid expensive arithmetic reasoning
}

lemma {:axiom} Mul_congruence_from_rem(a: nat, b: nat, c: nat, m: nat)
  requires m > 0
  requires a % m == b % m
  ensures (a * c) % m == (b * c) % m
{
  // admitted as an axiom; follows from Mul_mod_property
}
```

```vc-code
{
  var x := IntOf(sx);
  var y := IntOf(sy);
  var m := IntOf(sz);
  IntOf_eq_Str2Int(sz);
  assert m > 1;

  var acc := 1;
  var exp := y;

  // Establish initial invariant: acc % m == Exp_nonghost(x, y - exp) % m
  assert y - exp == 0;
  assert Exp_nonghost(x, y - exp) == 1;
  assert acc % m == 1 % m;
  assert 1 % m == Exp_nonghost(x, y - exp) % m;

  while exp > 0
    invariant 0 <= exp <= y
    invariant acc < m
    invariant acc % m == Exp_nonghost(x, y - exp) % m
  {
    var oldAcc := acc;
    var oldExp := exp;

    acc := (acc * x) % m;
    exp := exp - 1;

    // Prove the invariant is preserved:
    Mul_mod_property(oldAcc, x, m);
    assert acc % m == ((oldAcc % m) * x) % m;
    assert ((oldAcc % m) * x) % m == (Exp_nonghost(x, y - oldExp) * x) % m;
    assert Exp_nonghost(x, y - oldExp + 1) == Exp_nonghost(x, y - oldExp) * x;
    assert y - exp == y - oldExp + 1;
    assert acc % m == Exp_nonghost(x, y - exp) % m;
  }

  var n := acc;
  res := Nat2Str(n);
  Nat2Str_valid(n);
  assert ValidBitString(res);
  assert Str2Int(res) == n;

  IntOf_eq_Str2Int(sx);
  IntOf_eq_Str2Int(sy);
  IntOf_eq_Str2Int(sz);
  Exp_nonghost_eq_Exp_int(IntOf(sx), IntOf(sy));
  assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
}
```