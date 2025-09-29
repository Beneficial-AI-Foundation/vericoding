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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
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
function Nat2Str(v: nat): string
  decreases v
{
  if v == 0 then "" else Nat2Str(v / 2) + (if v % 2 == 1 then "1" else "0")
}

lemma Nat2Str_correct(v: nat)
  ensures ValidBitString(Nat2Str(v))
  ensures Str2Int(Nat2Str(v)) == v
  decreases v
{
  if v == 0 {
    // Nat2Str(0) == "" and Str2Int("") == 0 by definition
  } else {
    Nat2Str_correct(v / 2);
    var s := Nat2Str(v / 2);
    var c := if v % 2 == 1 then "1" else "0";
    assert |s + c| > 0;
    assert (s + c)[0..|s + c| - 1] == s;
    assert (s + c)[|s + c| - 1] == c[0];
    assert Str2Int(s + c) == 2 * Str2Int(s) + (if c[0] == '1' then 1 else 0);
    assert Str2Int(s) == v / 2;
    assert Str2Int(s + c) == v;
    assert (c == "0" || c == "1");
    assert ValidBitString(s + c);
  }
}

function Exp_int_m(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then 1 else x * Exp_int_m(x, y - 1)
}

lemma Exp_int_equiv(x: nat, y: nat)
  ensures Exp_int_m(x, y) == Exp_int(x, y)
  decreases y
{
  if y == 0 {
  } else {
    Exp_int_equiv(x, y - 1);
  }
}

lemma ValidBitString_prefix(s: string, j: int)
  requires ValidBitString(s)
  requires 0 <= j <= |s|
  ensures ValidBitString(s[0..j])
{
  assert forall k | 0 <= k < j :: s[0..j][k] == '0' || s[0..j][k] == '1';
}

lemma Str2Int_prefix_char(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var t := s[0..i+1];
  ValidBitString_prefix(s, i+1);
  ValidBitString_prefix(t, i);
  assert t[0..|t|-1] == s[0..i];
  assert t[|t|-1] == s[i];
  assert Str2Int(t) == 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
  assert Str2Int(t) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
}

lemma Str2Int_preserve_equality(s: string, t: string)
  requires s == t
  requires ValidBitString(s)
  requires ValidBitString(t)
  ensures Str2Int(s) == Str2Int(t)
  decreases |s|
{
  if |s| == 0 {
    // both are empty -> both Str2Int = 0
  } else {
    // reduce to prefixes
    var sp := s[0..|s|-1];
    var tp := t[0..|t|-1];
    assert |t| == |s|;
    assert sp == tp;
    Str2Int_preserve_equality(sp, tp);
    // now use definition on last character
    assert Str2Int(s) == 2 * Str2Int(sp) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(t) == 2 * Str2Int(tp) + (if t[|t|-1] == '1' then 1 else 0);
    assert s[|s|-1] == t[|t|-1];
    assert Str2Int(s) == Str2Int(t);
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
  // Parse sx into x
  var x := 0;
  var i := 0;
  while i < |sx|
    invariant 0 <= i <= |sx|
    invariant x == Str2Int(sx[0..i])
    invariant ValidBitString(sx[0..i])
  {
    var b := if sx[i] == '1' then 1 else 0;
    var oldx := x;
    var oldi := i;
    x := 2 * x + b;
    i := i + 1;
    // use lemma to connect prefixes
    Str2Int_prefix_char(sx, oldi);
    assert oldx == Str2Int(sx[0..oldi]);
    assert x == Str2Int(sx[0..i]);
    // maintain ValidBitString(sx[0..i]) using helper
    ValidBitString_prefix(sx, i);
  }
  // After finishing the loop, i == |sx| and x equals Str2Int(sx)
  assert i == |sx|;
  assert sx[0..i] == sx;
  assert x == Str2Int(sx[0..i]);
  ValidBitString_prefix(sx, i);
  Str2Int_preserve_equality(sx[0..i], sx);
  assert x == Str2Int(sx);

  // Parse sy into y
  var y := 0;
  i := 0;
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant y == Str2Int(sy[0..i])
    invariant ValidBitString(sy[0..i])
  {
    var b := if sy[i] == '1' then 1 else 0;
    var oldy := y;
    var oldi := i;
    y := 2 * y + b;
    i := i + 1;
    Str2Int_prefix_char(sy, oldi);
    assert oldy == Str2Int(sy[0..oldi]);
    assert y == Str2Int(sy[0..i]);
    ValidBitString_prefix(sy, i);
  }
  // After finishing the loop, i == |sy| and y equals Str2Int(sy)
  assert i == |sy|;
  assert sy[0..i] == sy;
  assert y == Str2Int(sy[0..i]);
  ValidBitString_prefix(sy, i);
  Str2Int_preserve_equality(sy[0..i], sy);
  assert y == Str2Int(sy);

  // Parse sz into m
  var m := 0;
  i := 0;
  while i < |sz|
    invariant 0 <= i <= |sz|
    invariant m == Str2Int(sz[0..i])
    invariant ValidBitString(sz[0..i])
  {
    var b := if sz[i] == '1' then 1 else 0;
    var oldm := m;
    var oldi := i;
    m := 2 * m + b;
    i := i + 1;
    Str2Int_prefix_char(sz, oldi);
    assert oldm == Str2Int(sz[0..oldi]);
    assert m == Str2Int(sz[0..i]);
    ValidBitString_prefix(sz, i);
  }
  // After finishing the loop, i == |sz| and m equals Str2Int(sz)
  assert i == |sz|;
  assert sz[0..i] == sz;
  assert m == Str2Int(sz[0..i]);
  ValidBitString_prefix(sz, i);
  Str2Int_preserve_equality(sz[0..i], sz);
  assert m == Str2Int(sz);

  // m > 1 by precondition on sz
  assert m > 1;

  // Compute value v = Exp_int_m(x,y) % m
  var v := Exp_int_m(x, y) % m;

  // Convert v to bitstring
  res := Nat2Str(v);

  // Prove postconditions by chaining equalities/lemmas
  Nat2Str_correct(v);
  Exp_int_equiv(x, y);
  assert Exp_int_m(x, y) == Exp_int(x, y);
  assert Str2Int(res) == v;
  assert v == Exp_int(x, y) % m;
  return;
}
// </vc-code>

