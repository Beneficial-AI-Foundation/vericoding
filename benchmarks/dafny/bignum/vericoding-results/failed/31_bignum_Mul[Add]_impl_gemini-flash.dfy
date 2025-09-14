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
function Multiply(s1: string, s2: string): string
  requires ValidBitString(s1)
  requires ValidBitString(s2)
  ensures ValidBitString(Multiply(s1, s2))
  ensures Str2Int(Multiply(s1, s2)) == Str2Int(s1) * Str2Int(s2)
  decreases Str2Int(s2)
{
  if s2 == "0" then
    "0"
  else if s2 == "1" then
    s1
  else
    var lastChar := s2[|s2| - 1];
    var s2_prefix := s2[0 .. |s2| - 1];
    var term1 := Multiply(s1, s2_prefix);
    var shifted_term1 := (if Str2Int(term1) == 0 then "0" else term1 + "0"); // Equivalent to multiplying by 2
    
    if lastChar == '1' then
      Add(shifted_term1, s1)
    else
      shifted_term1
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var len1 := |s1|;
  var len2 := |s2|;
  var maxLen := if len1 > len2 then len1 else len2;
  var i := 0;
  var carry := 0;
  var resultChars: array<char> := new char[maxLen + 1]; // +1 for potential carry

  while i < maxLen || carry > 0
    invariant 0 <= i <= maxLen + 1 
    invariant 0 <= carry <= 1
    invariant forall k :: 0 <= k < i ==> (resultChars[k] == '0' || resultChars[k] == '1')
    decreases maxLen - i + carry // Simplification of decreases clause as detailed invariant is not used for loop termination
  {
    var bit1 := if i < len1 then (if s1[len1 - 1 - i] == '1' then 1 else 0) else 0;
    var bit2 := if i < len2 then (if s2[len2 - 1 - i] == '1' then 1 else 0) else 0;

    var sum := bit1 + bit2 + carry;
    if i < maxLen + 1 { 
      resultChars[i] := if (sum % 2) == 1 then '1' else '0';
    }
    carry := sum / 2;
    i := i + 1;
  }

  var tempResChars: array<char>;
  if i > 0 && !(i == 1 && resultChars[0] == '0' && carry == 0) {
    tempResChars := resultChars[0 .. i];
  } else { // This handles the case where the result is "0" from extremely short inputs (e.g., "0" + "0")
    tempResChars := new char[1];
    tempResChars[0] := '0';
  }

  res := "";
  var k := |tempResChars| - 1;
  while k >= 0
    invariant -1 <= k < |tempResChars|
    invariant ValidBitString(res)
    invariant forall l :: 0 <= l < |res| :: res[l] == tempResChars[|tempResChars| - 1 - l]
    decreases k
  {
    res := res + tempResChars[k];
    k := k - 1;
  }
  
  if res == "" then res := "0"; 

  // Remove leading zeros unless it's just "0"
  if |res| > 1 && res[0] == '0' {
    var j := 0;
    while j < |res| - 1 && res[j] == '0'
      invariant 0 <= j < |res|
      invariant ValidBitString(res)
      invariant (forall l :: 0 <= l < j :: res[l] == '0')
      decreases |res| - j
    {
      j := j + 1;
    }
    res := res[j..];
  }
}

function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then
    "0"
  else if n == 1 then
    "1"
  else
    Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

ghost function Str2Int_FromChars(a: array<char>, len: int): nat
  requires len >= 0
  requires len <= |a|
  requires forall k :: 0 <= k < len ==> (a[k] == '0' || a[k] == '1')
  decreases len
{
  if len == 0 then 0
  else (if a[len - 1] == '1' then 1 else 0) + 2 * Str2Int_FromChars(a, len - 1)
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
  res := Multiply(s1, s2);
}
// </vc-code>

