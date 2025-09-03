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
lemma {:fuel 1} Str2IntAppendBit(s: string, isOne: bool)
  requires ValidBitString(s)
  ensures Str2Int(s + (if isOne then "1" else "0")) == 2 * Str2Int(s) + (if isOne then 1 else 0)
{
  var b := if isOne then "1" else "0";
  assert |s + b| > 0;
  assert Str2Int(s + b) == 2 * Str2Int((s + b)[0..|s + b|-1]) + (if (s + b)[|s + b|-1] == '1' then 1 else 0);
  assert (s + b)[0..|s + b|-1] == s;
  assert (s + b)[|s + b|-1] == b[0];
  if isOne {
    assert (if (s + b)[|s + b|-1] == '1' then 1 else 0) == 1;
  } else {
    assert (if (s + b)[|s + b|-1] == '1' then 1 else 0) == 0;
  }
  assert Str2Int(s + b) == 2 * Str2Int(s) + (if isOne then 1 else 0);
}

method NatToBin(x: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == x
  decreases x
{
  if x == 0 {
    s := "";
    assert Str2Int(s) == 0;
    assert ValidBitString(s);
    return;
  } else {
    var q := x / 2;
    var r := x % 2;
    var s2 := NatToBin(q);
    if r == 1 {
      s := s2 + "1";
      Str2IntAppendBit(s2, true);
      assert Str2Int(s) == 2 * Str2Int(s2) + 1;
      assert Str2Int(s) == 2 * q + 1;
      assert Str2Int(s) == x;
      assert ValidBitString(s);
    } else {
      s := s2 + "0";
      Str2IntAppendBit(s2, false);
      assert Str2Int(s) == 2 * Str2Int(s2) + 0;
      assert Str2Int(s) == 2 * q;
      assert Str2Int(s) == x;
      assert ValidBitString(s);
    }
  }
}

lemma ModBound(x: nat, m: nat)
  requires m > 0
  ensures x % m < m
  decreases x
{
  if x < m {
    assert x % m == x;
    assert x % m < m;
  } else {
    ModBound(x - m, m);
    assert x % m == (x - m) % m;
    assert (x - m) % m < m;
    assert x % m < m;
  }
}

lemma ExpDouble(x: nat, y: nat)
  ensures Exp_int(x, 2*y) == Exp_int(x, y) * Exp_int(x, y)
  decreases y
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, 0) == Exp_int(x, 0) * Exp_int(x, 0);
  } else {
    // Exp_int(x, 2*y) = x * x * Exp_int(x, 2*(y-1))
    // Use inductive hypothesis on y-1
    ExpDouble(x, y - 1);
    // unfold definitions twice:
    assert Exp_int(x, 2*y) == x * Exp_int(x, 2*y - 1);
    assert Exp_int(x, 2*y - 1) == x * Exp_int(x, 2*y - 2);
    assert Exp_int(x, 2*y) == x * x * Exp_int(x, 2*y - 2);
    // By IH Exp_int(x, 2*y - 2) == Exp_int(x, y - 1) * Exp_int(x, y - 1)
    assert Exp_int(x, 2*y - 2) == Exp_int(x, y - 1) * Exp_int(x, y - 1);
    // So Exp_int(x, 2*y) == x*x*Exp_int(x,y-1)*Exp_int(x,y-1)
    // And Exp_int(x, y) == x * Exp_int(x, y - 1)
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    // Hence RHS equals LHS
    assert Exp_int(x, y) * Exp_int(x, y) == x * x * Exp_int(x, y - 1) * Exp_int(x, y - 1);
    assert Exp_int(x, 2*y) == Exp_int(x, y) * Exp_int(x, y);
  }
}

lemma ExpSplitBit(x: nat, y: nat, b: bool)
  ensures Exp_int(x, 2*y + (if b then 1 else 0)) == Exp_int(x, y) * Exp_int(x, y) * (if b then x else 1)
  decreases y
{
  if b {
    // Exp_int(x, 2*y + 1) = x * Exp_int(x, 2*y) = x * (Exp_int(x,y)*Exp_int(x,y))
    ExpDouble(x, y);
    assert Exp_int(x, 2*y + 1) == x * Exp_int(x, 2*y);
    assert Exp_int(x, 2*y) == Exp_int(x, y) * Exp_int(x, y);
    assert Exp_int(x, 2*y + 1) == Exp_int(x, y) * Exp_int(x, y) * x;
  } else {
    ExpDouble(x, y);
    assert Exp_int(x, 2*y) == Exp_int(x, y) * Exp_int(x, y);
  }
}

lemma MulMod(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m) * (b % m) % m == (a * b) % m
{
  var r1 := a % m;
  var r2 := b % m;
  var q1 := a / m;
  var q2 := b / m;
  assert a == q1 * m + r1;
  assert b == q2 * m + r2;
  // a*b = (q1*m + r1)*(q2*m + r2) = m*(...) + r1*r2
  assert a * b == m * (q1 * q2 * m + q1 * r2 + q2 * r1) + r1 * r2;
  // hence (a*b) % m == (r1*r2) % m
  assert (a * b) % m == (r1 * r2) % m;
  // also (a % m) * (b % m) % m == (r1 * r2) % m
  assert (a % m) * (b % m) % m == (r1 * r2) % m;
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
  // process exponent by recursion on its bit-length (|sy|)
  if |sy| == 1 {
    // sy is either "0" or "1"
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
    var t := ModExp(sx, prefix, sz); // recursive call on shorter exponent
    var tval := Str2Int(t);
    // tval == Exp_int(base, Str2Int(prefix)) % m
    var newval := (tval * tval) % m;
    if lastIsOne {
      newval := (newval * base) % m;
    }
    // Convert back to binary string
    var s := NatToBin(newval);
    res := s;
    assert ValidBitString(res);
    // Now prove the numeric equality
    var yprefix := Str2Int(prefix);
    // Str2Int(sy) == 2*Str2Int(prefix) + (if lastIsOne then 1 else 0)
    Str2IntAppendBit(prefix, lastIsOne);
    // Use lemma about exponent splitting
    ExpSplitBit(base, yprefix, lastIsOne);
    // Relate modulo of product: (a % m)*(b % m) % m == (a*b) % m
    // Let full := Exp_int(base, yprefix)
    var full := Exp_int(base, yprefix);
    // From recursive call: tval == full % m
    assert tval == full % m;
    // newval (before possible multiply by base) equals (tval * tval) % m which equals (full*full) % m
    MulMod(full, full, m);
    assert (tval * tval) % m == (full * full) % m;
    if lastIsOne {
      // newval == ((full*full) % m * base) % m == (full*full*base) % m
      MulMod((full * full) % m, base, m);
      // But to get direct equality we show ((full*full) % m * base) % m == (full*full*base) % m
      // Using MulMod with a = full*full and b = base:
      MulMod(full * full, base, m);
      assert newval == (full * full * base) % m;
      assert newval == Exp_int(base, 2*yprefix + 1) % m;
    } else {
      // newval == (full*full) % m == Exp_int(base, 2*yprefix) % m
      assert newval == (full * full) % m;
      assert newval == Exp_int(base, 2*yprefix) % m;
    }
    // Combine with Str2IntAppendBit: Exp_int(base, Str2Int(sy)) == Exp_int(base, 2*yprefix + (if lastIsOne then 1 else 0))
    // Using ExpSplitBit we have equality to full*full*(if lastIsOne then base else 1)
    // Hence newval equals Exp_int(base, Str2Int(sy)) % m
    assert Str2Int(res) == newval;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  }
}
// </vc-code>

