ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function ExpNat(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * ExpNat(x, y - 1)
}

function StrToNat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * StrToNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

function Int2Str(k: nat): string
  ensures ValidBitString(Int2Str(k))
  ensures Str2Int(Int2Str(k)) == k
  decreases k
{
  if k == 0 then "" else Int2Str(k / 2) + (if k % 2 == 1 then "1" else "0")
}

lemma ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m * b % m) % m == (a * b) % m
{
  var q1 := a / m; var r1 := a % m;
  var q2 := b / m; var r2 := b % m;
  assert a == q1 * m + r1;
  assert b == q2 * m + r2;
  var p := q1*q2*m + q1*r2 + q2*r1;
  assert a * b == p * m + r1 * r2;
  assert (a * b) % m == (r1 * r2) % m;
  assert (a % m * b % m) % m == (r1 * r2) % m;
}

lemma ExpNat_add(x: nat, a: nat, b: nat)
  ensures ExpNat(x, a + b) == ExpNat(x, a) * ExpNat(x, b)
  decreases b
{
  if b == 0 {
    assert ExpNat(x, a + 0) == ExpNat(x, a) * ExpNat(x, 0);
  } else {
    ExpNat_add(x, a, b - 1);
    assert ExpNat(x, a + b) == if a + b == 0 then 1 else x * ExpNat(x, a + b - 1);
    assert ExpNat(x, b) == if b == 0 then 1 else x * ExpNat(x, b - 1);
    assert ExpNat(x, a) * ExpNat(x, b) == ExpNat(x, a) * (x * ExpNat(x, b - 1));
    assert ExpNat(x, a) * (x * ExpNat(x, b - 1)) == x * (ExpNat(x, a) * ExpNat(x, b - 1));
    assert x * (ExpNat(x, a) * ExpNat(x, b - 1)) == x * ExpNat(x, a + b - 1);
    assert x * ExpNat(x, a + b - 1) == ExpNat(x, a + b);
  }
}

lemma ExpNat_double(x: nat, e: nat)
  ensures ExpNat(x, 2 * e) == ExpNat(x, e) * ExpNat(x, e)
{
  ExpNat_add(x, e, e);
}

lemma ExpNat_eq_Exp_int(x: nat, y: nat)
  ensures ExpNat(x,y) == Exp_int(x,y)
  decreases y
{
  if y == 0 {
    assert ExpNat(x,0) == 1;
    assert Exp_int(x,0) == 1;
  } else {
    ExpNat_eq_Exp_int(x, y-1);
    assert ExpNat(x,y) == x * ExpNat(x,y-1);
    assert Exp_int(x,y) == x * Exp_int(x,y-1);
    assert ExpNat(x,y-1) == Exp_int(x,y-1);
  }
}

lemma StrToNat_eq_Str2Int(s: string)
  requires ValidBitString(s)
  ensures StrToNat(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
    assert StrToNat(s) == 0;
    assert Str2Int(s) == 0;
  } else {
    StrToNat_eq_Str2Int(s[0..|s|-1]);
    var pref := s[0..|s|-1];
    assert StrToNat(s) == 2 * StrToNat(pref) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(pref) + (if s[|s|-1] == '1' then 1 else 0);
    assert StrToNat(pref) == Str2Int(pref);
  }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  var x := StrToNat(sx);
  var m := StrToNat(sz);
  var zero := true;
  var idx := 0;
  while idx < |sy|
  {
    if sy[idx] == '1' {
      zero := false;
      break;
    }
    idx := idx + 1;
  }
  if zero {
    res := Int2Str(1 % m);
    return;
  }
  var cur := x % m;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant cur == ExpNat(x, ExpNat(2, i)) % m
    decreases n - i
  {
    assert cur == ExpNat(x, ExpNat(2, i)) % m;
    ModMul(cur, cur, m);
    ModMul(ExpNat(x, ExpNat(2, i)), ExpNat(x, ExpNat(2, i)), m);
    assert (cur * cur) % m == (ExpNat(x, ExpNat(2, i)) * ExpNat(x, ExpNat(2, i))) % m;
    ExpNat_double(x, ExpNat(2, i));
    assert ExpNat(x, ExpNat(2, i + 1)) == ExpNat(x, ExpNat(2, i)) * ExpNat(x, ExpNat(2, i));
    cur := (cur * cur) % m;
    i := i + 1;
  }
  res := Int2Str(cur);
}
// </vc-code>

