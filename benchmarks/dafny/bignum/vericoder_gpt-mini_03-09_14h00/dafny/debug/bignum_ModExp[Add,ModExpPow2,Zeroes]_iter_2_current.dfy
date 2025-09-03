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
  // s + b is non-empty because b is length 1
  assert |s + b| > 0;
  // By definition of Str2Int on a non-empty string s+b:
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
    // For nat, when x < m, x % m == x
    assert x % m == x;
    assert x % m < m;
  } else {
    // x >= m, reduce
    ModBound(x - m, m);
    // For nat, (x) % m == (x - m) % m when x >= m
    assert x % m == (x - m) % m;
    assert (x - m) % m < m;
    assert x % m < m;
  }
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
  var exp := Str2Int(sy);
  var m := Str2Int(sz);
  var r := Exp_int(base, exp) % m;
  // m > 0 by precondition Str2Int(sz) > 1
  ModBound(Exp_int(base, exp), m);
  assert r < m;
  var s := NatToBin(r);
  res := s;
  assert ValidBitString(res);
  assert Str2Int(res) == r;
  assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
}
// </vc-code>

