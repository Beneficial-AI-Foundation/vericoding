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
function Nat2Str(v: nat): string
  ensures ValidBitString(Nat2Str(v))
  ensures Str2Int(Nat2Str(v)) == v
  decreases v
{
  if v == 0 then "0" else
    if v / 2 == 0 then (if v % 2 == 1 then "1" else "0")
    else Nat2Str(v / 2) + (if v % 2 == 1 then "1" else "0")
}

lemma Exp_add(x: nat, m: nat, n: nat)
  ensures Exp_int(x, m + n) == Exp_int(x, m) * Exp_int(x, n)
  decreases n
{
  if n == 0 {
  } else {
    Exp_add(x, m, n - 1);
    assert Exp_int(x, m + n) == x * Exp_int(x, m + n - 1);
    assert Exp_int(x, m) * Exp_int(x, n) == Exp_int(x, m) * (x * Exp_int(x, n - 1));
    assert Exp_int(x, m + n - 1) == Exp_int(x, m) * Exp_int(x, n - 1);
    assert x * Exp_int(x, m + n - 1) == x * (Exp_int(x, m) * Exp_int(x, n - 1));
  }
}

lemma Exp2_double(i: nat)
  ensures Exp_int(2, i+1) == Exp_int(2, i) + Exp_int(2, i)
  decreases i
{
  if i == 0 {
    // Exp_int(2,1) == 2 and Exp_int(2,0) == 1
  } else {
    Exp2_double(i - 1);
    // Exp_int(2, i+1) == 2 * Exp_int(2, i)
    assert Exp_int(2, i+1) == 2 * Exp_int(2, i);
    assert Exp_int(2, i) + Exp_int(2, i) == 2 * Exp_int(2, i);
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
  assert a * b == qa * qb * z * z + qa * z * rb + qb * z * ra + ra * rb;
  assert (a * b) % z == (ra * rb) % z;
  assert (ra * rb) % z == (ra % z) * (rb % z) % z;
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
    var big := Exp_int(2, i); // exponent 2^i
    // prove that (oldv*oldv)%z equals Exp_int(Str2Int(sx), Exp_int(2, i+1)) % z
    MulMod(Exp_int(Str2Int(sx), big), Exp_int(Str2Int(sx), big), z);
    // Use Exp_add on the exponents: Exp_int(x, m+n) == Exp_int(x,m)*Exp_int(x,n)
    Exp_add(Str2Int(sx), big, big);
    Exp2_double(i);
    assert oldv == Exp_int(Str2Int(sx), big) % z by {
      assert Exp_int(Str2Int(sx), big) % z == Exp_int(Str2Int(sx), Exp_int(2, i)) % z;
      assert oldv == Exp_int(Str2Int(sx), Exp_int(2, i)) % z;
    }
    v := (oldv * oldv) % z;
    assert v == (Exp_int(Str2Int(sx), big) * Exp_int(Str2Int(sx), big)) % z;
    assert (Exp_int(Str2Int(sx), big) * Exp_int(Str2Int(sx), big)) % z == Exp_int(Str2Int(sx), big + big) % z;
    assert big + big == Exp_int(2, i+1);
    assert v == Exp_int(Str2Int(sx), Exp_int(2, i+1)) % z;
    i := i + 1;
  }
  res := Nat2Str(v);
}
// </vc-code>

