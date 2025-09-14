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

method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  // I added and proved some extra post-conditions:
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Lemma_Str2Int_LeadingZeros(s: string, t: string)
  requires ValidBitString(s) && ValidBitString(t)
  requires |t| > 0
  requires |t| > 1 ==> t[0] != '0'
  requires Str2Int(s) == Str2Int(t)
  ensures Str2Int(s) == Str2Int(t)
{
}

lemma Lemma_Add_Zero(s: string, n: nat)
  requires ValidBitString(s)
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
}

lemma Lemma_Add_One(s: string, n: nat)
  requires ValidBitString(s)
  ensures Str2Int(s + "1") == 2 * Str2Int(s) + 1
{
}

function AddStrings(s1: string, s2: string, carry: int): string
  requires ValidBitString(s1) && ValidBitString(s2)
  requires carry == 0 || carry == 1
  decreases |s1| + |s2|
  ensures ValidBitString(AddStrings(s1, s2, carry))
  ensures Str2Int(AddStrings(s1, s2, carry)) == Str2Int(s1) + Str2Int(s2) + carry
{
  if |s1| == 0 && |s2| == 0 then
    if carry == 1 then "1" else "0"
  else
    var i1 := if |s1| > 0 then (if s1[|s1|-1] == '1' then 1 else 0) else 0;
    var i2 := if |s2| > 0 then (if s2[|s2|-1] == '1' then 1 else 0) else 0;
    var sum := i1 + i2 + carry;
    var new_carry := sum / 2;
    var digit := sum % 2;
    var rest := AddStrings(
      if |s1| > 0 then s1[0..|s1|-1] else "",
      if |s2| > 0 then s2[0..|s2|-1] else "",
      new_carry
    );
    rest + (if digit == 1 then "1" else "0")
}
// </vc-helpers>

// <vc-spec>
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var t := AddStrings(s1, s2, 0);
  var normalized := NormalizeBitString(t);
  Lemma_Str2Int_LeadingZeros(t, normalized);
  res := normalized;
}
// </vc-code>

