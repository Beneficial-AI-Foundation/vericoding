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

lemma {:auto} Str2Int_concat(u: string, v: string)
  requires ValidBitString(u) && ValidBitString(v)
  ensures Str2Int(u + v) == Str2Int(u) * pow2(|v|) + Str2Int(v)
  decreases v
{
  if |v| == 0 {
    // u + "" == u, pow2(0) == 1, Str2Int("") == 0
  } else {
    var vp := v[0..|v|-1];
    var last := v[|v|-1..|v|];
    // (u + v) = (u + vp) + last
    Str2Int_concat(u, vp);
    Pow2_Succ(|vp|);
    // Now reason by definitions/induction:
    // Str2Int(u + v) == 2 * Str2Int((u+v)[0..|u+v|-1]) + (if last == "1" then 1 else 0)
    // (u+v)[0..|u+v|-1] == u + vp
    // By IH: Str2Int(u+vp) == Str2Int(u)*pow2(|vp|) + Str2Int(vp)
    // So Str2Int(u+v) == 2*(Str2Int(u)*pow2(|vp|) + Str2Int(vp)) + Str2Int(last)
    // pow2(|v|) == 2 * pow2(|vp|)
    // Str2Int(v) == 2*Str2Int(vp) + Str2Int(last)
    // hence Str2Int(u+v) == Str2Int(u)*pow2(|v|) + Str2Int(v)
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
  // Compute integer value a = Str2Int(s1)
  var a := 0;
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant ValidBitString(s1)
    invariant a == Str2Int(s1[0..i])
  {
    var bit := if s1[i] == '1' then 1 else 0;
    a := 2 * a + bit;
    i := i + 1;
  }

  // Compute integer value b = Str2Int(s2)
  var b := 0;
  i := 0;
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant ValidBitString(s2)
    invariant b == Str2Int(s2[0..i])
  {
    var bit := if s2[i] == '1' then 1 else 0;
    b := 2 * b + bit;
    i := i + 1;
  }

  // Product
  var p := a * b;
  var orig := p;

  // Build result string t by prepending bits (so t becomes MSB-first)
  var t := "";
  var k := 0;
  // Invariant: orig == Str2Int(t) + p * pow2(k)
  while p > 0
    invariant p >= 0
    invariant ValidBitString(t)
    invariant k >= 0
    invariant orig == Str2Int(t) + p * pow2(k)
  {
    var bitstr := if p % 2 == 1 then "1" else "0";
    // prepend the LSB we extracted
    t := bitstr + t;
    p := p / 2;
    k := k + 1;
  }

  if orig == 0 {
    // Represent zero as empty string (valid and Str2Int("") == 0)
    res := "";
  } else {
    res := t;
  }
}
// </vc-code>

