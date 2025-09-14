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
lemma BitStringRep(n: nat)
  ensures exists s:string :: ValidBitString(s) && Str2Int(s) == n
  decreases n
{
  if n == 0 {
    // empty string represents 0
    assert ValidBitString("");
    assert Str2Int("") == 0;
    assert exists s: string :: ValidBitString(s) && Str2Int(s) == n;
  } else {
    // Inductive step: use n = 2*(n/2) + (n%2)
    BitStringRep(n/2);
    var s0 :| ValidBitString(s0) && Str2Int(s0) == n/2;

    var t := s0 + (if n % 2 == 1 then "1" else "0");

    // Prove ValidBitString(t)
    assert forall i :: 0 <= i < |t| ==> t[i] == '0' || t[i] == '1' by {
      if i < |s0| {
        // Characters from s0 preserve validity
      } else {
        assert |t| == |s0| + 1;
        assert i == |s0|;
        assert t[i] == (if n % 2 == 1 then '1' else '0');
      }
    }

    // Unfold Str2Int to compute Str2Int(t)
    reveal Str2Int();
    assert |t| > 0;
    assert |t| == |s0| + 1;
    assert t[0..|t|-1] == s0;
    assert t[|t|-1] == (if n % 2 == 1 then '1' else '0');

    assert Str2Int(t) ==
      2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
    assert Str2Int(t) == 2
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
lemma BitStringRep(n: nat)
  ensures exists s:string :: ValidBitString(s) && Str2Int(s) == n
  decreases n
{
  if n == 0 {
    // empty string represents 0
    assert ValidBitString("");
    assert Str2Int("") == 0;
    assert exists s: string :: ValidBitString(s) && Str2Int(s) == n;
  } else {
    // Inductive step: use n = 2*(n/2) + (n%2)
    BitStringRep(n/2);
    var s0 :| ValidBitString(s0) && Str2Int(s0) == n/2;

    var t := s0 + (if n % 2 == 1 then "1" else "0");

    // Prove ValidBitString(t)
    assert forall i :: 0 <= i < |t| ==> t[i] == '0' || t[i] == '1' by {
      if i < |s0| {
        // Characters from s0 preserve validity
      } else {
        assert |t| == |s0| + 1;
        assert i == |s0|;
        assert t[i] == (if n % 2 == 1 then '1' else '0');
      }
    }

    // Unfold Str2Int to compute Str2Int(t)
    reveal Str2Int();
    assert |t| > 0;
    assert |t| == |s0| + 1;
    assert t[0..|t|-1] == s0;
    assert t[|t|-1] == (if n % 2 == 1 then '1' else '0');

    assert Str2Int(t) ==
      2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
    assert Str2Int(t) == 2
// </vc-code>

