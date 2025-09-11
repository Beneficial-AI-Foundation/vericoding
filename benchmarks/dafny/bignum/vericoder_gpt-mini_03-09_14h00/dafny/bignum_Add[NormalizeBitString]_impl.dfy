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
  ensures ValidBitString(NatToBitString(n))
  ensures Str2Int(NatToBitString(n)) == n
  ensures |NatToBitString(n)| > 0
  ensures |NatToBitString(n)| > 1 ==> NatToBitString(n)[0] != '0'
  decreases n
{
  if n == 0 then
    "0"
  else if n / 2 == 0 then
    (if n % 2 == 1 then "1" else "0")
  else
    NatToBitString(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma SubstringIsValid(s: string, a: int, b: int)
  requires ValidBitString(s)
  requires 0 <= a <= b <= |s|
  ensures ValidBitString(s[a..b])
{
  var m := b - a;
  var k := 0;
  while k < m
    invariant 0 <= k <= m
    invariant forall i | 0 <= i < k :: s[a..b][i] == '0' || s[a..b][i] == '1'
  {
    // s[a+k] is within bounds and is '0' or '1' by ValidBitString(s)
    assert 0 <= a + k < |s|;
    assert s[a + k] == '0' || s[a + k] == '1';
    // relation between substring indexing and original string
    assert s[a..b][k] == s[a + k];
    k := k + 1;
  }
}

lemma ParseStep(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
{
  // Ensure the prefix is a valid bitstring so Str2Int can be applied
  SubstringIsValid(s, 0, i+1);
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
  SubstringIsValid(s1, 0, 0);
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant ValidBitString(s1)
    invariant ValidBitString(s1[0..i])
    invariant n1 == Str2Int(s1[0..i])
  {
    var bit := if s1[i] == '1' then 1 else 0;
    // Relate numeric update to Str2Int for the extended prefix
    ParseStep(s1, i);
    // establish validity of next prefix s1[0..i+1]
    SubstringIsValid(s1, 0, i + 1);
    n1 := 2 * n1 + bit;
    // Now n1 corresponds to the extended prefix
    assert n1 == Str2Int(s1[0..i+1]);
    i := i + 1;
  }

  // Parse s2 to integer n2
  var j := 0;
  var n2: nat := 0;
  // establish invariants for j = 0
  SubstringIsValid(s2, 0, 0);
  while j < |s2|
    invariant 0 <= j <= |s2|
    invariant ValidBitString(s2)
    invariant ValidBitString(s2[0..j])
    invariant n2 == Str2Int(s2[0..j])
  {
    var bit := if s2[j] == '1' then 1 else 0;
    ParseStep(s2, j);
    SubstringIsValid(s2, 0, j + 1);
    n2 := 2 * n2 + bit;
    assert n2 == Str2Int(s2[0..j+1]);
    j := j + 1;
  }

  // Construct result from numeric sum
  res := NatToBitString(n1 + n2);
}
// </vc-code>

