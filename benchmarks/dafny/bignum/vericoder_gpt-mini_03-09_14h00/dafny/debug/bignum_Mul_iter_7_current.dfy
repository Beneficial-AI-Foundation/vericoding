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

// <vc-helpers>
lemma EvenDecomp(n: nat)
  ensures 2*(n/2) + n%2 == n
  decreases n
{
  if n == 0 { }
  else {
    EvenDecomp(n/2);
  }
}

lemma Str2Int_Push(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2*Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  assert |s[0..i+1]| == i+1;
  assert Str2Int(s[0..i+1]) == 2 * Str2Int((s[0..i+1])[0..|s[0..i+1]|-1]) + (if (s[0..i+1])[|s[0..i+1]|-1] == '1' then 1 else 0);
  assert (s[0..i+1])[|s[0..i+1]|-1] == s[i];
  assert (s[0..i+1])[0..|s[0..i+1]|-1] == s[0..i];
  assert Str2Int(s[0..i+1]) == 2*Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
}

lemma Str2Int_prefix_full(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s[0..|s|]) == Str2Int(s)
{
  if |s| == 0 { }
  else {
    var i := |s| - 1;
    Str2Int_Push(s, i);
    // By definition Str2Int(s) == 2*Str2Int(s[0..i]) + (if s[i]=='1' then 1 else 0),
    // and Str2Int_Push gives Str2Int(s[0..|s|]) == the same RHS.
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
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var p := n1 * n2;
  res := BinOf(p);
}
// </vc-code>

