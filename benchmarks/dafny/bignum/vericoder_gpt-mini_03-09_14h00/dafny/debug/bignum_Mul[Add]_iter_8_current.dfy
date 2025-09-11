ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

lemma {:auto} Pow2_Succ(n: nat)
  ensures pow2(n + 1) == 2 * pow2(n)
  decreases n
{
  if n == 0 {
  } else {
    Pow2_Succ(n - 1);
  }
}

lemma ValidLiteral0()
  ensures ValidBitString("0")
{
  forall j | 0 <= j < 1
  {
    assert "0"[j] == '0' || "0"[j] == '1';
  }
}

lemma ValidLiteral1()
  ensures ValidBitString("1")
{
  forall j | 0 <= j < 1
  {
    assert "1"[j] == '0' || "1"[j] == '1';
  }
}

lemma SubstringValid(s: string, lo: nat, hi: nat)
  requires ValidBitString(s)
  requires 0 <= lo <= hi <= |s|
  ensures ValidBitString(s[lo..hi])
{
  forall j | 0 <= j < hi - lo
  {
    assert s[lo..hi][j] == s[lo + j];
    assert 0 <= lo + j < |s|;
    assert s[lo + j] == '0' || s[lo + j] == '1';
  }
}

lemma Str2Int_prefix_step(s: string, i: nat)
  requires ValidBitString(s)
  requires i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var pref := s[0..i+1];
  assert Str2Int(pref) == (if |pref| == 0 then 0 else 2 * Str2Int(pref[0..|pref|-1]) + (if pref[|pref|-1] == '1' then 1 else 0));
  assert |pref| == i + 1;
  assert |pref| != 0;
  assert Str2Int(pref) == 2 * Str2Int(pref[0..|pref|-1]) + (if pref[|pref|-1] == '1' then 1 else 0);
  assert pref[0..|pref|-1] == s[0..i];
  assert pref[|pref|-1] == s[i];
  assert Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
}

lemma CharValue(c: string)
  requires ValidBitString(c)
  requires |c| == 1
  ensures Str2Int(c) == (if c[0] == '1' then 1 else 0)
{
  assert Str2Int(c) == (if |c| == 0 then 0 else 2 * Str2Int(c[0..|c|-1]) + (if c[|c|-1] == '1' then 1 else 0));
  assert |c| != 0;
  assert |c| == 1;
  assert c[0..|c|-1] == "";
  assert Str2Int("") == 0;
  assert Str2Int(c) == 2 * 0 + (if c[0] == '1' then 1 else 0);
  assert Str2Int(c) == (if c[0] == '1' then 1 else 0);
}

lemma Str2Int_concat(u: string, v: string)
  requires ValidBitString(u) && ValidBitString(v)
  ensures Str2Int(u + v) == Str2Int(u) * pow2(|v|) + Str2Int(v)
  decreases |v|
{
  if |v| == 0 {
    assert pow2(0) == 1;
    assert Str2Int("") == 0;
    assert Str2Int(u + "") == Str2Int(u);
    assert Str2Int(u) * pow2(0) + Str2Int("") == Str2Int(u);
  } else {
    var vp := v[0..|v|-1];
    var last := v[|v|-1..|v|];
    SubstringValid(v, 0, |v|-1);
    SubstringValid(v, |v|-1, |v|);
    // By definition on u+v:
    assert Str2Int(u + v) == (if |u + v| == 0 then 0 else 2 * Str2Int((u + v)[0..|u + v|-1]) + (if (u + v)[|u + v|-1] == '1' then 1 else 0));
    assert |u + v| != 0;
    // (u+v)[0..|u+v|-1] == u + vp
    assert (u + v)[0..|u + v|-1] == u + vp;
    assert (u + v)[|u + v|-1] == last[0];
    assert Str2Int(u + v) == 2 * Str2Int(u + vp) + (if last[0] == '1' then 1 else 0);
    // apply induction to Str2Int(u + vp)
    Str2Int_concat(u, vp);
    // apply prefix step to v to relate Str2Int(v)
    Str2Int_prefix_step(v, |v| - 1);
    // compute:
    assert Str2Int(u + vp) == Str2Int(u) * pow2(|vp|) + Str2Int(vp);
    assert Str2Int(v) == 2 * Str2Int(vp) + (if last[0] == '1' then 1 else 0);
    // combine:
    assert 2 * (Str2Int(u) * pow2(|vp|) + Str2Int(vp)) + (if last[0] == '1' then 1 else 0) == Str2Int(u) * (2 * pow2(|vp|)) + (2 * Str2Int(vp) + (if last[0] == '1' then 1 else 0));
    Pow2_Succ(|vp|);
    assert 2 * pow2(|vp|) == pow2(|vp| + 1);
    assert Str2Int(u + v) == Str2Int(u) * pow2(|vp| + 1) + Str2Int(v);
    assert |vp| + 1 == |v|;
    assert Str2Int(u + v) == Str2Int(u) * pow2(|v|) + Str2Int(v);
  }
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  // Parse s1 into a non-ghost integer n1, with a ghost proof that n1 == Str2Int(s1)
  var n1 := 0;
  ghost var g1 := Str2Int("");
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant n1 >= 0
    decreases |s1| - i
  {
    var bit := if s1[i] == '1' then 1 else 0;
    n1 := 2 * n1 + bit;
    ghost {
      // g1 == Str2Int(s1[0..i])
      assert g1 == Str2Int(s1[0..i]);
      Str2Int_prefix_step(s1, i);
      // Update ghost accumulator to prefix length i+1
      g1 := Str2Int(s1[0..i+1]);
      assert bit == (if s1[i] == '1' then 1 else 0);
      assert g1 == n1;
    }
    i := i + 1;
  }

  // Parse s2 into a non-ghost integer n2, with a ghost proof that n2 == Str2Int(s2)
  var n2 := 0;
  ghost var g2 := Str2Int("");
  i := 0;
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant n2 >= 0
    decreases |s2| - i
  {
    var bit := if s2[i] == '1' then 1 else 0;
    n2 := 2 * n2 + bit;
    ghost {
      assert g2 == Str2Int(s2[0..i]);
      Str2Int_prefix_step(s2, i);
      g2 := Str2Int(s2[0..i+1]);
      assert bit == (if s2[i] == '1' then 1 else 0);
      assert g2 == n2;
    }
    i := i + 1;
  }

  var p := n1 * n2;
  res := "";
  var x := p;
  // Invariant: x * pow2(|res|) + Str2Int(res) == p, and res is valid
  while x > 0
    invariant ValidBitString(res)
    invariant x * pow2(|res|) + Str2Int(res) == p
    decreases x
  {
    var oldRes := res;
    var xold := x;
    var b := xold % 2;
    var bit := if b == 1 then "1" else "0";
    var newRes := bit + oldRes;
    x := xold / 2;
    // perform non-ghost assignments before any lemma calls
    res := newRes;

    // Now prove the invariant holds using lemmas (ghost)
    if b == 1 {
      ValidLiteral1();
    } else {
      ValidLiteral0();
    }
    CharValue(bit);
    assert Str2Int(bit) == (if bit[0] == '1' then 1 else 0);
    // bit[0] == '1' iff b == 1, so:
    assert Str2Int(bit) == b;
    Str2Int_concat(bit, oldRes);
    assert Str2Int(newRes) == Str2Int(bit) * pow2(|oldRes|) + Str2Int(oldRes);
    assert xold == 2 * x + b;
    Pow2_Succ(|oldRes|);
    assert 2 * pow2(|oldRes|) == pow2(|oldRes| + 1);
    assert 2 * x * pow2(|oldRes|) == x * pow2(|oldRes| + 1);
    assert b * pow2(|oldRes|) + Str2Int(oldRes) == Str2Int(newRes);
    assert x * pow2(|newRes|) + Str2Int(newRes) == p;
  }
  if |res| == 0 {
    // if res is empty then p == 0, produce "0"
    assert x == 0;
    assert Str2Int(res) == p;
    res := "0";
    ValidLiteral0();
    CharValue(res);
    assert Str2Int(res) == 0;
  }
}
// </vc-code>

