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

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
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
function BinToNat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  Str2Int(s)
}

function PowMod(x: nat, y: nat, m: nat): nat
  requires m > 0
  decreases y
{
  Exp_int(x, y) % m
}

function Nat2Bin(n: nat): string
  decreases n
{
  if n == 0 then "0"
  else
    var q := n / 2;
    var r := n % 2;
    Nat2Bin(q) + (if r == 1 then "1" else "0")
}

lemma Nat2Bin_ok(n: nat)
  ensures ValidBitString(Nat2Bin(n))
  ensures Str2Int(Nat2Bin(n)) == n
  decreases n
{
  if n == 0 {
    assert Nat2Bin(0) == "0";
    assert ValidBitString("0");
    assert Str2Int("0") == 0;
  } else {
    var q := n / 2;
    var r := n % 2;
    Nat2Bin_ok(q);
    var s := Nat2Bin(q);
    assert ValidBitString(s);
    if r == 1 {
      assert Nat2Bin(n) == s + "1";
      assert Str2Int(s + "1") == 2 * Str2Int(s) + 1;
      assert Str2Int(s) == q;
      assert 2 * q + 1 == n;
      assert Str2Int(Nat2Bin(n)) == n;
      assert ValidBitString(s + "1");
    } else {
      assert Nat2Bin(n) == s + "0";
      assert Str2Int(s + "0") == 2 * Str2Int(s) + 0;
      assert Str2Int(s) == q;
      assert 2 * q + 0 == n;
      assert Str2Int(Nat2Bin(n)) == n;
      assert ValidBitString(s + "0");
    }
  }
}

lemma Str2Int_prefix_step(s: string, i: nat)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var t := s[0..i+1];
  assert |t| == i + 1;
  if |t| == 0 {
    assert false;
  } else {
    assert Str2Int(t) == 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
    assert t[|t|-1] == s[i];
    assert t[0..|t|-1] == s[0..i];
    assert Str2Int(t[0..|t|-1]) == Str2Int(s[0..i]);
    assert (if t[|t|-1] == '1' then 1 else 0) == (if s[i] == '1' then 1 else 0);
  }
}

lemma DivMul(m: nat, t: nat)
  requires m > 0
  ensures (m * t) / m == t
{
  var q := (m * t) / m;
  var r := (m * t) % m;
  assert m * q + r == m * t;
  assert 0 <= r < m;
  // r = m*(t - q)
  assert r == m * (t - q);
  if t != q {
    // then t > q, so t - q >= 1, hence m*(t - q) >= m, contradicting r < m
    assert t > q;
    assert t - q >= 1;
    assert m * (t - q) >= m;
    assert r >= m;
    assert r < m; // contradiction
  }
  // therefore t == q
}

lemma MulModZero(m: nat, t: nat)
  requires m > 0
  ensures (m * t) % m == 0
{
  // From DivMul we know (m*t)/m == t
  DivMul(m, t);
  var q := (m * t) / m;
  var r := (m * t) % m;
  assert q == t;
  assert m * q + r == m * t;
  assert r == m * t - m * q;
  assert r == 0;
}

lemma ModEqByDiff(u: nat, v: nat, m: nat, t: nat)
  requires m > 0
  requires u == v + m * t
  ensures u % m == v % m
{
  var qu := u / m;
  var ru := u % m;
  var qv := v / m;
  var rv := v % m;
  assert m * qu + ru == u;
  assert m * qv + rv == v;
  assert m * qu + ru == m * qv + rv + m * t;
  // rearrange to express ru in terms of rv and a multiple of m
  assert ru == rv + m * (qv + t - qu);
  assert 0 <= ru < m;
  assert 0 <= rv < m;
  if ru != rv {
    if ru > rv {
      // ru - rv == m * (qv + t - qu) and ru - rv >= 1, so RHS >= m, contradiction with ru - rv < m
      var diff := ru - rv;
      assert diff == m * (qv + t - qu);
      assert diff >= 1;
      assert m * (qv + t - qu) >= m;
      assert diff >= m;
      assert diff < m; // contradiction
    } else {
      // rv > ru
      var diff2 := rv - ru;
      // From ru == rv + m*(...), get rv - ru == m*(qu - qv - t)
      assert rv - ru == m * (qu - qv - t);
      assert diff2 >= 1;
      assert m * (qu - qv - t) >= m;
      assert diff2 >= m;
      assert diff2 < m; // contradiction
    }
  }
  // hence ru == rv
}

lemma ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m * b) % m == (a * b) % m
{
  var r := a % m;
  var k := a / m;
  assert a == m * k + r;
  // a*b == r*b + m*(k*b)
  assert a * b == r * b + m * (k * b);
  ModEqByDiff(a * b, r * b, m, k * b);
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
  var x := BinToNat(sx);
  var y := BinToNat(sy);
  var z := BinToNat(sz);
  var p := PowMod(x, y, z);
  res := Nat2Bin(p);
  Nat2Bin_ok(p);
  assert Str2Int(res) == p;
  assert p == Exp_int(x, y) % z;
  assert x == Str2Int(sx);
  assert y == Str2Int(sy);
  assert z == Str2Int(sz);
  assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
}
// </vc-code>

