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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function NatToBin(n: nat): string
  decreases n
  ensures ValidBitString(result)
  ensures Str2Int(result) == n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else
    var q := n / 2;
    var r := n % 2;
    NatToBin(q) + (if r == 1 then "1" else "0")
}

lemma Str2IntAppendBit(prefix: string, b: bool)
  requires ValidBitString(prefix)
  ensures ValidBitString(prefix + (if b then "1" else "0"))
  ensures Str2Int(prefix + (if b then "1" else "0")) == 2 * Str2Int(prefix) + (if b then 1 else 0)
{
  var s := prefix + (if b then "1" else "0");
  assert |s| == |prefix| + 1;
  assert s[|s|-1] == (if b then '1' else '0');
  assert s[0..|s|-1] == prefix;
  if |s| == 0 {
  } else {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s[0..|s|-1]) == Str2Int(prefix);
    assert (if s[|s|-1] == '1' then 1 else 0) == (if b then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if b then 1 else 0);
  }
}

lemma Exp_int_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a) * 1;
    assert Exp_int(x, 0) == 1;
  } else {
    Exp_int_add(x, a, b - 1);
    assert Exp_int(x, a + b) == x * Exp_int(x, a + b - 1);
    assert Exp_int(x, a + b - 1) == Exp_int(x, a) * Exp_int(x, b - 1);
    assert x * Exp_int(x, a + b - 1) == Exp_int(x, a) * (x * Exp_int(x, b - 1));
    assert x * Exp_int(x, b - 1) == Exp_int(x, b);
    assert Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b);
  }
}

lemma ExpSplitBit(base: nat, yprefix: nat, b: bool)
  ensures Exp_int(base, 2*yprefix + (if b then 1 else 0)) ==
          Exp_int(base, yprefix) * Exp_int(base, yprefix) * (if b then base else 1)
{
  Exp_int_add(base, yprefix, yprefix);
  assert Exp_int(base, yprefix + yprefix) == Exp_int(base, yprefix) * Exp_int(base, yprefix);
  if b {
    assert Exp_int(base, 2*yprefix + 1) == base * Exp_int(base, 2*yprefix);
    assert Exp_int(base, 2*yprefix) == Exp_int(base, yprefix) * Exp_int(base, yprefix);
    assert Exp_int(base, 2*yprefix + 1) == base * (Exp_int(base, yprefix) * Exp_int(base, yprefix));
    assert Exp_int(base, 2*yprefix + 1) == Exp_int(base, yprefix) * Exp_int(base, yprefix) * base;
  } else {
    assert Exp_int(base, 2*yprefix + 0) == Exp_int(base, 2*yprefix);
    assert Exp_int(base, 2*yprefix) == Exp_int(base, yprefix) * Exp_int(base, yprefix);
  }
}

lemma MulMod(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
  var ra := a % m;
  var rb := b % m;
  var qa := a / m;
  var qb := b / m;
  assert a == m * qa + ra;
  assert b == m * qb + rb;
  var prod := a * b;
  assert prod == m * (qa * (m * qb) + qa * rb + ra * qb) + ra * rb;
  assert (a * b) % m == (ra * rb) % m;
  assert ra % m == ra;
  assert rb % m == rb;
  assert (ra * rb) % m == ((ra % m) * (rb % m)) % m;
  assert (a * b) % m == ((a % m) * (b % m)) % m;
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
  var base := Str2Int(sx);
  var m := Str2Int(sz);
  if |sy| == 1 {
    var b := (if sy[|sy|-1] == '1' then 1 else 0);
    var v := Exp_int(base, b) % m;
    var s := NatToBin(v);
    res := s;
    assert ValidBitString(res);
    assert Str2Int(res) == v;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    return;
  } else {
    var prefix := sy[0..|sy|-1];
    var lastIsOne := sy[|sy|-1] == '1';
    var t := ModExp(sx, prefix, sz);
    var tval := Str2Int(t);
    var newval := (tval * tval) % m;
    if lastIsOne {
      newval := (newval * base) % m;
    }
    var s := NatToBin(newval);
    res := s;
    assert ValidBitString(res);
    var yprefix := Str2Int(prefix);
    assert sy == prefix + (if lastIsOne then "1" else "0");
    Str2IntAppendBit(prefix, lastIsOne);
    assert Str2Int(sy) == 2 * Str2Int(prefix) + (if lastIsOne then 1 else 0);
    var full := Exp_int(base, yprefix);
    assert tval == full % m;
    MulMod(full, full, m);
    assert (tval * tval) % m == (full * full) % m;
    if lastIsOne {
      MulMod((full * full) % m, base, m);
      MulMod(full * full, base, m);
      assert newval == (full * full * base) % m;
      ExpSplitBit(base, yprefix, true);
      assert newval == Exp_int(base, 2 * yprefix + 1) % m;
    } else {
      assert newval == (full * full) % m;
      ExpSplitBit(base, yprefix, false);
      assert newval == Exp_int(base, 2 * yprefix) % m;
    }
    assert Str2Int(res) == newval;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  }
}
// </vc-code>

