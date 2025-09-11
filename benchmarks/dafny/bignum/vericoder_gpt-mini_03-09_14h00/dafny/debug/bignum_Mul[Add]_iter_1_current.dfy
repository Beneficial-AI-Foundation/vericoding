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
    // Str2Int(u + "") == Str2Int(u) * pow2(0) + Str2Int("")
    // Str2Int("") == 0 and pow2(0) == 1 by definitions
  } else {
    var vp := v[0..|v|-1];
    var last := v[|v|-1..|v|];
    // Str2Int(u+v) = 2 * Str2Int((u+v)[0..|u+v|-1]) + bit(last of v)
    // but (u+v)[0..|u+v|-1] == u+vp
    Str2Int_concat(u, vp);
    // pow2(|v|) == 2 * pow2(|vp|)
    Pow2_Succ(|vp|);
    // Using definitions:
    // Str2Int(u+v) = 2*Str2Int(u+vp) + (if last == "1" then 1 else 0)
    // By IH: Str2Int(u+vp) = Str2Int(u)*pow2(|vp|) + Str2Int(vp)
    // So Str2Int(u+v) = 2*(Str2Int(u)*pow2(|vp|) + Str2Int(vp
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

lemma {:auto} Str2Int_concat(u: string, v: string)
  requires ValidBitString(u) && ValidBitString(v)
  ensures Str2Int(u + v) == Str2Int(u) * pow2(|v|) + Str2Int(v)
  decreases v
{
  if |v| == 0 {
    // Str2Int(u + "") == Str2Int(u) * pow2(0) + Str2Int("")
    // Str2Int("") == 0 and pow2(0) == 1 by definitions
  } else {
    var vp := v[0..|v|-1];
    var last := v[|v|-1..|v|];
    // Str2Int(u+v) = 2 * Str2Int((u+v)[0..|u+v|-1]) + bit(last of v)
    // but (u+v)[0..|u+v|-1] == u+vp
    Str2Int_concat(u, vp);
    // pow2(|v|) == 2 * pow2(|vp|)
    Pow2_Succ(|vp|);
    // Using definitions:
    // Str2Int(u+v) = 2*Str2Int(u+vp) + (if last == "1" then 1 else 0)
    // By IH: Str2Int(u+vp) = Str2Int(u)*pow2(|vp|) + Str2Int(vp)
    // So Str2Int(u+v) = 2*(Str2Int(u)*pow2(|vp|) + Str2Int(vp
// </vc-code>

