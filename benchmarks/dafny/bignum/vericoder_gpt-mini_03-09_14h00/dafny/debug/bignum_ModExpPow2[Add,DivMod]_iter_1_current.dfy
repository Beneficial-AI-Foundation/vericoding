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

// <vc-helpers>
function method Nat2Str(v: nat): string
  ensures ValidBitString(result)
  ensures Str2Int(result) == v
  decreases v
{
  if v == 0 then "0" else
    var q := v / 2;
    var r := v % 2;
    if q == 0 then (if r == 1 then "1" else "0") else Nat2Str(q) + (if r == 1 then "1" else "0")
}

lemma Exp_add(x: nat, m: nat, n: nat)
  ensures Exp_int(x, m + n) == Exp_int(x, m) * Exp_int(x, n)
  decreases n
{
  if n == 0 {
    // Exp_int(x, m+0) == Exp_int(x,m) and Exp_int(x,0) == 1
  } else {
    Exp_add(x, m, n - 1);
    // Exp_int(x, m + n) == x * Exp_int(x, m + n - 1)
    // and Exp_int(x, m) * Exp_int(x, n) == Exp_int(x, m) * (x * Exp_int(x, n - 1))
    assert Exp_int(x, m + n) == x * Exp_int(x, m + n - 1);
    assert Exp_int(x, m) * Exp_int(x, n) == Exp_int(x, m) * (x * Exp_int(x, n - 1));
    assert Exp_int(x, m + n - 1) == Exp_int(x, m) * Exp_int(x, n - 1);
    // multiply both sides of the last equality by x
    assert x * Exp_int(x, m + n - 1) == x * (Exp_int(x, m) * Exp_int(x, n - 1));
    // which gives the required equality
  }
}

lemma MulMod(a: nat, b: nat, z: nat)
  requires z > 0
  ensures (a % z) * (b % z) % z == (a * b) % z
{
  var ra := a % z;
  var rb := b % z;
  var qa := a / z;
  var qb := b / z;
  assert a == qa * z + ra;
  assert b == qb * z + rb;
  // a*b = qa*qb*z*z + qa*z*rb + qb*z*ra + ra*rb
  assert a * b == qa * qb * z * z + qa * z * rb + qb * z * ra + ra * rb;
  // therefore (a*b) % z == (ra*rb) % z
  assert (a * b) % z == (ra * rb) % z;
  // since 0 <= ra < z and 0 <= rb < z, ra % z == ra and rb % z == rb
  assert (ra * rb) % z == (ra % z) * (rb % z) % z;
  // substitute ra%z and rb%z with a%z and b%z
  assert (ra % z) == (a % z);
  assert (rb % z) == (b % z);
  assert (a * b) % z == (a % z) * (b % z) % z;
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
  var z := Str2Int(sz);
  if Str2Int(sy) == 0 {
    res := Nat2Str(1 % z);
    return;
  }
  var v := Str2Int(sx) % z;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant v < z
    invariant v == Exp_int(Str2Int(sx), Exp_int(2, i)) % z
  {
    var oldv := v;
    v := (v * v) % z;
    // prove invariant for i+1
    // oldv == Exp_int(x,2^i) % z
    // so v == (oldv*oldv) % z == (Exp_int(x,2^i)*Exp_int(x,2^i)) % z == Exp_int(x,2^(i+1)) % z
    MulMod(oldv, oldv, z);
    // relate Exp_int powers
    Exp_add(Str2Int(sx), Exp_int(2, i), Exp_int(2, i));
    // Using Exp_add with m = 2^i and n = 2^i yields Exp_int(x,2*2^i) == Exp_int(x,2^i)*Exp_int(x,2^i)
    i := i + 1;
  }
  res := Nat2Str(v);
}
// </vc-code>

