//ATOM


// ----------------------------------------------------
// string-based addition (no Str2Int / Int2Str)
// ----------------------------------------------------
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
    res := "";
    assume ValidBitString(res);
    assume Str2Int(res) == Str2Int(s1) + Str2Int(s2);
    return res;
}


//ATOM


method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  // I added and proved some extra post-conditions:
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
    t := "";
    assume ValidBitString(t);
    assume |t| > 0;
    assume |t| > 1 ==> t[0] != '0';
    assume ValidBitString(s) ==> Str2Int(s) == Str2Int(t);
    return t;
}


//ATOM


// Make an opaque version to speed up verification
opaque function OStr2Int(s: string): nat
  requires ValidBitString(s)
{
  Str2Int(s)
}


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


//IMPL Mul

// ----------------------------------------------------
// string-based multiplication
//    No direct use of Str2Int/Int2Str
// ----------------------------------------------------
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  res := "0";
  var i := 0;
  var shifted := s1;
  
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant ValidBitString(res)
    invariant ValidBitString(shifted)
    invariant Str2Int(shifted) == Str2Int(s1) * pow2(i)
    invariant Str2Int(res) == Str2Int(s1) * Str2IntPrefix(s2, i)
  {
    if s2[|s2| - 1 - i] == '1' {
      res := Add(res, shifted);
    }
    
    if i + 1 < |s2| {
      shifted := shifted + "0";
    }
    
    i := i + 1;
  }
}

function pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

function Str2IntPrefix(s: string, k: nat): nat
  requires ValidBitString(s)
  requires 0 <= k <= |s|
{
  if k == 0 then 0
  else (if s[|s| - k] == '1' then pow2(k - 1) else 0) + Str2IntPrefix(s, k - 1)
}