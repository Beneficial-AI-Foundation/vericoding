// <vc-preamble>
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{

  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method NormalizeBitString(s: string) returns(t: string)

  ensures ValidBitString(t)

  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

method CompareUnequal(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  requires |s1| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 0
  requires |s2| > 1 ==> s2[0] != '0'
  requires |s1| > |s2|
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Introduce a let-binding for slice length to fix a parsing error */
function CompareRecursive(s1: string, s2: string): int
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2|
  ensures Str2Int(s1) < Str2Int(s2) ==> result == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> result == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> result == 1
  decreases |s1|
{
  if |s1| == 0 then 0
  else
    let len := |s1| - 1 in
    let r := CompareRecursive(s1[..len], s2[..len]) in
    if r != 0 then r
    else if s1[len] < s2[len] then -1
    else if s1[len] > s2[len] then 1
    else 0
}

/* helper modified by LLM (iteration 10): proves that Str2Int("0" + tail) == Str2Int(tail) */
lemma Str2Int_leading_zero(tail: string)
  requires ValidBitString(tail)
  ensures Str2Int("0" + tail) == Str2Int(tail)
  decreases |tail|
{
  if |tail| == 0 {
    // Str2Int("0") is 0, Str2Int("") is 0.
  } else {
    // Str2Int("0" + tail) = 2 * Str2Int("0" + tail[..|tail|-1]) + last_bit.
    // Str2Int(tail) = 2 * Str2Int(tail[..|tail|-1]) + last_bit.
    // Recursively, Str2Int("0" + prefix) == Str2Int(prefix)
    Str2Int_leading_zero(tail[..|tail|-1]);
  }
}

/* helper modified by LLM (iteration 10): proves that leading zeros do not affect the integer value */
lemma ZerosPrefixEquiv(s: string, i: nat)
  requires ValidBitString(s)
  requires i <= |s|
  requires forall k :: 0 <= k < i ==> s[k] == '0'
  ensures Str2Int(s) == Str2Int(s[i..])
  decreases i
{
  if i > 0 {
    Str2Int_leading_zero(s[1..]);
    ZerosPrefixEquiv(s[1..], i - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): implement normalization inline and use helpers to prove correctness */
  var i1 := 0;
  while i1 < |s1| - 1 && s1[i1] == '0'
    invariant 0 <= i1 <= |s1|
    invariant ValidBitString(s1)
    invariant forall k :: 0 <= k < i1 ==> s1[k] == '0'
  {
    i1 := i1 + 1;
  }
  ZerosPrefixEquiv(s1, i1);
  var norm_s1 := s1[i1..];
  
  var i2 := 0;
  while i2 < |s2| - 1 && s2[i2] == '0'
    invariant 0 <= i2 <= |s2|
    invariant ValidBitString(s2)
    invariant forall k :: 0 <= k < i2 ==> s2[k] == '0'
  {
    i2 := i2 + 1;
  }
  ZerosPrefixEquiv(s2, i2);
  var norm_s2 := s2[i2..];

  if |norm_s1| < |norm_s2| {
    res := -1;
  } else if |norm_s1| > |norm_s2| {
    res := 1;
  } else {
    res := CompareRecursive(norm_s1, norm_s2);
  }
}
// </vc-code>
