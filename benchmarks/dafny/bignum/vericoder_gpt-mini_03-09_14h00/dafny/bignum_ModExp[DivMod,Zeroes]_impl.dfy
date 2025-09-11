ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
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
  decreases s
  ensures IntOf(s) == Str2Int(s)
{
  if |s| == 0 {
  } else {
    var s0 := s[0..|s|-1];
    IntOf_eq_Str2Int(s0);
  }
}

lemma Exp_nonghost_eq_Exp_int(x: nat, y: nat)
  decreases y
  ensures Exp_nonghost(x,y) == Exp_int(x,y)
{
  if y == 0 {
  } else {
    Exp_nonghost_eq_Exp_int(x, y-1);
  }
}

lemma Exp_mod_compat(x: nat, y: nat, m: nat)
  requires m > 0
  decreases y
  ensures Exp_nonghost(x % m, y) % m == Exp_nonghost(x, y) % m
{
  if y == 0 {
  } else {
    Exp_mod_compat(x, y-1, m);
    var k := x / m;
    assert x == x % m + m * k;
  }
}

function Nat2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Nat2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Nat2Str_valid(n: nat)
  decreases n
  ensures ValidBitString(Nat2Str(n))
  ensures Str2Int(Nat2Str(n)) == n
{
  if n == 0 {
  } else {
    var q := n / 2;
    var r := n % 2;
    Nat2Str_valid(q);
  }
}

lemma Mul_mod_property(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * b) % m
{
  var k := a / m;
  assert a == a % m + m * k;
  assert a * b == (a % m) * b + m * (k * b);
}

lemma Mul_congruence_from_rem(a: nat, b: nat, c: nat, m: nat)
  requires m > 0
  requires a % m == b % m
  ensures (a * c) % m == (b * c) % m
{
  Mul_mod_property(a, c, m);
  Mul_mod_property(b, c, m);
  assert (a * c) % m == ((a % m) * c) % m;
  assert (b * c) % m == ((b % m) * c) % m;
  assert a % m == b % m;
  assert ((a % m) * c) % m == ((b % m) * c) % m;
  assert (a * c) % m == (b * c) % m;
}

lemma Rem_lt(a: nat, m: nat)
  requires m > 0
  ensures a % m < m
{
  var q := a / m;
  assert a == (a % m) + m * q;
  assert a % m < m;
}
// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1)
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases |sy|
// </vc-spec>
// <vc-code>
{
  var x := IntOf(sx);
  var y := IntOf(sy);
  var m := IntOf(sz);
  IntOf_eq_Str2Int(sz);
  assert m > 1;

  var acc := 1;
  var exp := y;

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

    Mul_mod_property(oldAcc, x, m);
    assert acc % m == ((oldAcc % m) * x) % m;

    assert oldAcc % m == Exp_nonghost(x, y - oldExp) % m;
    Mul_congruence_from_rem(oldAcc, Exp_nonghost(x, y - oldExp), x, m);
    assert ((oldAcc % m) * x) % m == (Exp_nonghost(x, y - oldExp) * x) % m;

    assert Exp_nonghost(x, y - oldExp + 1) == Exp_nonghost(x, y - oldExp) * x;
    assert y - exp == y - oldExp + 1;
    assert acc % m == Exp_nonghost(x, y - exp) % m;

    Rem_lt(acc, m);
    assert acc < m;
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
// </vc-code>

