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
function NatToBitString(n: nat): string
  ensures ValidBitString(result)
  ensures Str2Int(result) == n
  ensures |result| > 0
  ensures |result| > 1 ==> result[0] != '0'
{
  if n == 0 then
    "0"
  else
    var prefix := NatToBitString(n / 2);
    if n / 2 == 0 then
      (if n % 2 == 1 then "1" else "0")
    else
      prefix + (if n % 2 == 1 then "1" else "0")
}

lemma SubstringIsValid(s: string, a: int, b: int)
  requires ValidBitString(s)
  requires 0 <= a <= b <= |s|
  ensures ValidBitString(s[a..b])
{
  var m := b - a;
  forall k | 0 <= k < m
  {
    var idx := a + k;
    assert 0 <= idx < |s|;
    assert s[idx] == '0' || s[idx] == '1';
    assert s[a..b][k] == s[idx];
    assert s[a..b][k] == '0' || s[a..b][k] == '1';
  }
}

lemma ParseStep(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  // |s[0..i+1]| = i+1 > 0, so the definition of Str2Int yields the equality.
  assert |s[0..i+1]| == i+1;
  if |s[0..i+1]| == 0 {
    assert false;
  } else {
    assert Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
  }
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
  // Parse s1 to integer n1
  var i := 0;
  var n1: nat := 0;
  // establish invariants for i = 0
  call SubstringIsValid(s1, 0, 0);
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant ValidBitString(s1)
    invariant ValidBitString(s1[0..i])
    invariant n1 == Str2Int(s1[0..i])
  {
    var bit := if s1[i] == '1' then 1 else 0;
    n1 := 2 * n1 + bit;
    // relate numeric update to Str2Int for the extended prefix
    call ParseStep(s1, i);
    // establish validity of next prefix
    call SubstringIsValid(s1, i, i + 1);
    i := i + 1;
  }

  // Parse s2 to integer n2
  var j := 0;
  var n2: nat := 0;
  // establish invariants for j = 0
  call SubstringIsValid(s2, 0, 0);
  while j < |s2|
    invariant 0 <= j <= |s2|
    invariant ValidBitString(s2)
    invariant ValidBitString(s2[0..j])
    invariant n2 == Str2Int(s2[0..j])
  {
    var bit := if s2[j] == '1' then 1 else 0;
    n2 := 2 * n2 + bit;
    call ParseStep(s2, j);
    call SubstringIsValid(s2, j, j + 1);
    j := j + 1;
  }

  // Construct result from numeric sum
  res := NatToBitString(n1 + n2);
}
// </vc-code>

