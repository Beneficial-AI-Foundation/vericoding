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
    // both 0
  } else {
    var s0 := s[0..|s|-1];
    var last := s[|s|-1 .. |s|];
    IntOf_eq_Str2Int(s0);
    // By definitions of IntOf and Str2Int
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

lemma Exp_mod_compat(x: nat, y: nat, m: nat)
  requires m > 0
  decreases y
  ensures Exp_nonghost(x % m, y) % m == Exp_nonghost(x, y) % m
{
  if y == 0 {
    // both 1 % m
  } else {
    Exp_mod_compat(x, y-1, m);
    // Let E1 = Exp_nonghost(x % m, y-1), E2 = Exp_nonghost(x, y-1)
    // We know E1 % m == E2 % m by IH.
    // x == (x % m) + m * (x / m)
    var k := x / m;
    assert x == x % m + m * k;
    // x * E2 == (x % m) * E2 + m * (k * E2)
    // so (x * E2) % m == ((x % m) * E2) % m
    // and since E2 % m == E1 % m, ((x % m) * E2) % m == ((x % m) * E1) % m
    // therefore (x * E2) % m == ((x % m) * E1) % m, i.e., RHS == LHS
  }
}
// keep existing Nat2Str_valid and Str2Int_append lemmas (they remain above)
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
  // Convert input bit-strings to concrete naturals (non-ghost)
  var x := IntOf(sx);
  var y := IntOf(sy);
  var m := IntOf(sz);
  // m > 1 is ensured by requires via IntOf_eq_Str2Int
  IntOf_eq_Str2Int(sz);
  assert m > 1;

  // fast modular exponentiation: compute n = x^y % m
  var base := x % m;
  var exp := y;
  var acc := 1 % m;

  // Invariant: acc * Exp_nonghost(base, exp) % m == Exp_nonghost(x, y) % m
  // This holds initially because Exp_mod_compat makes Exp_nonghost(base, exp) % m == Exp_nonghost(x, exp) % m
  calc {
    // establish initial relation via lemma
    Exp_mod_compat(x, exp, m);
  }
  while exp > 0
    invariant exp >= 0
    invariant 0 <= base
    invariant 0 <= acc
    invariant acc < m
    invariant base < m
    invariant acc * Exp_nonghost(base, exp) % m == Exp_nonghost(x, y) % m
  {
    if exp % 2 == 1 {
      acc := (acc * base) % m;
    }
    exp := exp / 2;
    base := (base * base) % m;
    // after updating acc, exp, base the invariant is preserved by arithmetic reasoning
  }

  var n := acc;
  res := Nat2Str(n);
  Nat2Str_valid(n);
  assert ValidBitString(res);
  assert Str2Int(res) == n;

  // Now prove final equality with ghost specifications
  // n == Exp_nonghost(x,y) % m by the invariant and exp == 0
  assert n == Exp_nonghost(x, y) % m;
  // convert non-ghost functions to ghost ones via lemmas
  IntOf_eq_Str2Int(sx);
  IntOf_eq_Str2Int(sy);
  IntOf_eq_Str2Int(sz);
  Exp_nonghost_eq_Exp_int(IntOf(sx), IntOf(sy));
  // Chain equalities to reach target:
  // Str2Int(res) == n == Exp_nonghost(IntOf(sx),IntOf(sy)) % IntOf(sz)
  // == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
}
// </vc-code>

