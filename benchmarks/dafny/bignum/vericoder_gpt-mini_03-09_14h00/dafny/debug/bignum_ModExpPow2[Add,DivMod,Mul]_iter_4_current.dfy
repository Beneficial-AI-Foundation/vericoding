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

lemma Exp_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    // Exp_int(x, a + 0) == Exp_int(x, a) * Exp_int(x, 0)
    assert Exp_int(x, a + 0) == Exp_int(x, a) * Exp_int(x, 0);
  } else {
    Exp_add(x, a, b - 1);
    assert Exp_int(x, a + b) == if a + b == 0 then 1 else x * Exp_int(x, a + b - 1);
    assert Exp_int(x, b) == if b == 0 then 1 else x * Exp_int(x, b - 1);
    assert Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a) * (x * Exp_int(x, b - 1));
    assert Exp_int(x, a) * (x * Exp_int(x, b - 1)) == x * (Exp_int(x, a) * Exp_int(x, b - 1));
    assert x * (Exp_int(x, a) * Exp_int(x, b - 1)) == x * Exp_int(x, a + b - 1);
    assert x * Exp_int(x, a + b - 1) == Exp_int(x, a + b);
  }
}

lemma Exp_double(x: nat, e: nat)
  ensures Exp_int(x, 2 * e) == Exp_int(x, e) * Exp_int(x, e)
{
  Exp_add(x, e, e);
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
  var x := Str2Int(sx);
  var m := Str2Int(sz);
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
    invariant cur == Exp_int(x, Exp_int(2, i)) % m
    decreases n - i
  {
    assert cur == Exp_int(x, Exp_int(2, i)) % m;
    ModMul(cur, cur, m);
    ModMul(Exp_int(x, Exp_int(2, i)), Exp_int(x, Exp_int(2, i)), m);
    assert (cur * cur) % m == (Exp_int(x, Exp_int(2, i)) * Exp_int(x, Exp_int(2, i))) % m;
    Exp_double(x, Exp_int(2, i));
    assert Exp_int(x, Exp_int(2, i + 1)) == Exp_int(x, Exp_int(2, i)) * Exp_int(x, Exp_int(2, i));
    cur := (cur * cur) % m;
    i := i + 1;
  }
  res := Int2Str(cur);
}
// </vc-code>

