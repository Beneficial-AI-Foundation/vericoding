//ATOM

// ----------------------------------------------------
// Str2Int: bit-string -> nat (reference function)
// ----------------------------------------------------
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}


//ATOM

predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}


//IMPL NormalizeBitString

method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  // I added and proved some extra post-conditions:
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  if |s| == 0 {
    t := "0";
    return;
  }
  
  // Find the first non-zero character
  var i := 0;
  while i < |s| && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant forall j | 0 <= j < i :: s[j] == '0'
  {
    i := i + 1;
  }
  
  if i == |s| {
    // All characters are '0', return "0"
    t := "0";
  } else {
    // Return substring from first non-zero character
    t := s[i..];
  }
}