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
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant ValidBitString(s1)
    invariant n1 == Str2Int(s1[0..i])
  {
    var bit := if s1[i] == '1' then 1 else 0;
    n1 := 2 * n1 + bit;
    i := i + 1;
  }

  // Parse s2 to integer n2
  var j := 0;
  var n2: nat := 0;
  while j < |s2|
    invariant 0 <= j <= |s2|
    invariant ValidBitString(s2)
    invariant n2 == Str2Int(s2[0..j])
  {
    var bit := if s2[j] == '1' then 1 else 0;
    n2 := 2 * n2 + bit;
    j := j + 1;
  }

  // Construct result from numeric sum
  res := NatToBitString(n1 + n2);
}
// </vc-code>

