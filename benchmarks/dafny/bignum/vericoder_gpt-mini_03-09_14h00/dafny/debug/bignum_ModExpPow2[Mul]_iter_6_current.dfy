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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function Int2Str(x: nat) returns (result: string)
  ensures ValidBitString(result)
  ensures Str2Int(result) == x
  decreases x
{
  if x == 0 then "" else Int2Str(x / 2) + (if x % 2 == 1 then "1" else "0")
}

lemma ExpAdd(a: nat, x: nat, y: nat)
  ensures Exp_int(a, x + y) == Exp_int(a, x) * Exp_int(a, y)
  decreases y
{
  if y == 0 {
    assert Exp_int(a, x + 0) == Exp_int(a, x) * 1;
    assert Exp_int(a, 0) == 1;
  } else {
    ExpAdd(a, x, y - 1);
    assert Exp_int(a, x + y) == a * Exp_int(a, x + y - 1);
    assert Exp_int(a, y) == a * Exp_int(a, y - 1);
    assert Exp_int(a, x + y - 1) == Exp_int(a, x) * Exp_int(a, y - 1);
    assert a * Exp_int(a, x + y - 1) == Exp_int(a, x) * (a * Exp_int(a, y - 1));
    assert Exp_int(a, x) * (a * Exp_int(a, y - 1)) == Exp_int(a, x) * Exp_int(a, y);
  }
}

lemma MulMod(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x * y) % m == ((x % m) * (y % m)) % m
{
  var qx := x / m;
  var rx := x % m;
  var qy := y / m;
  var ry := y % m;
  assert x == m * qx + rx;
  assert y == m * qy + ry;
  var prod := (m * qx + rx) * (m * qy + ry);
  assert x * y == prod;
  var k := m * qx * qy + qx * ry + qy * rx;
  assert prod == m * k + rx * ry;
  assert rx < m;
  assert ry < m;
  assert (m * k + rx * ry) % m == (rx * ry) % m;
  assert (rx * ry) % m == ((x % m) * (y % m)) % m;
}

lemma Exp2Succ(i: nat)
  ensures Exp_int(2, i + 1) == 2 * Exp_int(2, i)
{
  assert Exp_int(2, i + 1) == 2 * Exp_int(2, i);
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
  var m := Str2Int(sz);
  if Str2Int(sy) == 0 {
    res := Int2Str(1 % m);
    return;
  }
  var base := Str2Int(sx) % m;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant base < m
    invariant base == Exp_int(Str2Int(sx), Exp_int(2, i)) % m
    decreases n - i
  {
    var a := Exp_int(Str2Int(sx), Exp_int(2, i));
    MulMod(a, a, m);
    ExpAdd(Str2Int(sx), Exp_int(2, i), Exp_int(2, i));
    Exp2Succ(i);
    base := (base * base) % m;
    i := i + 1;
  }
  res := Int2Str(base);
}
// </vc-code>

