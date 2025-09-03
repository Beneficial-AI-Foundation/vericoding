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

ghost function Reverse(s: string): string
  decreases s
{
  if |s| == 0 then "" else s[|s|-1..|s|] + Reverse(s[0..|s|-1])
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

lemma SubstringValid(s: string, lo: nat, hi: nat)
  requires ValidBitString(s)
  requires 0 <= lo <= hi <= |s|
  ensures ValidBitString(s[lo..hi])
{
  // Prove each character in the substring is '0' or '1'
  forall j | 0 <= j < hi - lo
  {
    // s[lo..hi][j] is s[lo + j]
    assert s[lo..hi][j] == s[lo + j];
    assert 0 <= lo + j < |s|;
    assert s[lo + j] == '0' || s[lo + j] == '1' by (ValidBitString(s));
  }
}

lemma Str2Int_prefix_step(s: string, i: nat)
  requires ValidBitString(s)
  requires i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var pref := s[0..i+1];
  // By definition of Str2Int, Str2Int(pref) equals the unfolding:
  assert Str2Int(pref) == (if |pref| == 0 then 0 else 2 * Str2Int(pref[0..|pref|-1]) + (if pref[|pref|-1] == '1' then 1 else 0));
  assert |pref| == i + 1;
  assert |pref| != 0;
  assert Str2Int(pref) == 2 * Str2Int(pref[0..|pref|-1]) + (if pref[|pref|-1] == '1' then 1 else 0);
  // relate pref's pieces to s
  assert pref[0..|pref|-1] == s[0..i];
  assert pref[|pref|-1] == s[i];
  // substitute
  assert Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
}

lemma Str2Int_concat(u: string, v: string)
  requires ValidBitString(u) && ValidBitString(v)
  ensures Str2Int(u + v) == Str2Int(u) * pow2(|v|) + Str2Int(v)
  decreases |v|
{
  if |v| == 0 {
    // u + "" == u, pow2(0) == 1, Str2Int("") == 0
    assert pow2(0) == 1;
    assert Str2Int("") == 0;
    assert Str2Int(u + "") == Str2Int(u);
    assert Str2Int(u) * pow2(0) + Str2Int("") == Str2Int(u);
  } else {
    var vp := v[0..|v|-1];
    var last := v[|v|-1..|v|];
    // Substrings are valid
    SubstringValid(v, 0, |v|-1);
    SubstringValid(v, |v|-1, |v|);
    // Induction on vp
    Str2Int_concat(u, vp);
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
ghost function pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

ghost function Reverse(s: string): string
  decreases s
{
  if |s| == 0 then "" else s[|s|-1..|s|] + Reverse(s[0..|s|-1])
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

lemma SubstringValid(s: string, lo: nat, hi: nat)
  requires ValidBitString(s)
  requires 0 <= lo <= hi <= |s|
  ensures ValidBitString(s[lo..hi])
{
  // Prove each character in the substring is '0' or '1'
  forall j | 0 <= j < hi - lo
  {
    // s[lo..hi][j] is s[lo + j]
    assert s[lo..hi][j] == s[lo + j];
    assert 0 <= lo + j < |s|;
    assert s[lo + j] == '0' || s[lo + j] == '1' by (ValidBitString(s));
  }
}

lemma Str2Int_prefix_step(s: string, i: nat)
  requires ValidBitString(s)
  requires i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  var pref := s[0..i+1];
  // By definition of Str2Int, Str2Int(pref) equals the unfolding:
  assert Str2Int(pref) == (if |pref| == 0 then 0 else 2 * Str2Int(pref[0..|pref|-1]) + (if pref[|pref|-1] == '1' then 1 else 0));
  assert |pref| == i + 1;
  assert |pref| != 0;
  assert Str2Int(pref) == 2 * Str2Int(pref[0..|pref|-1]) + (if pref[|pref|-1] == '1' then 1 else 0);
  // relate pref's pieces to s
  assert pref[0..|pref|-1] == s[0..i];
  assert pref[|pref|-1] == s[i];
  // substitute
  assert Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
}

lemma Str2Int_concat(u: string, v: string)
  requires ValidBitString(u) && ValidBitString(v)
  ensures Str2Int(u + v) == Str2Int(u) * pow2(|v|) + Str2Int(v)
  decreases |v|
{
  if |v| == 0 {
    // u + "" == u, pow2(0) == 1, Str2Int("") == 0
    assert pow2(0) == 1;
    assert Str2Int("") == 0;
    assert Str2Int(u + "") == Str2Int(u);
    assert Str2Int(u) * pow2(0) + Str2Int("") == Str2Int(u);
  } else {
    var vp := v[0..|v|-1];
    var last := v[|v|-1..|v|];
    // Substrings are valid
    SubstringValid(v, 0, |v|-1);
    SubstringValid(v, |v|-1, |v|);
    // Induction on vp
    Str2Int_concat(u, vp);
// </vc-code>

