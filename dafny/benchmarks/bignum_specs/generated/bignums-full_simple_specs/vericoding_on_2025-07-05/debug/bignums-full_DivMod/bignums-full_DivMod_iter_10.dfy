//ATOM

// Make an opaque version to speed up verification
opaque function OStr2Int(s: string): nat
  requires ValidBitString(s)
{
  Str2Int(s)
}

//ATOM

// ----------------------------------------------------
// string-based subtraction (s1 >= s2)
// ----------------------------------------------------
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
    res := "";
    assume ValidBitString(res);
    assume Str2Int(res) == Str2Int(s1) - Str2Int(s2);
    return res;
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

method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
{
    res := 0;
    assume Str2Int(s1) < Str2Int(s2) ==> res == -1;
    assume Str2Int(s1) == Str2Int(s2) ==> res == 0;
    assume Str2Int(s1) > Str2Int(s2) ==> res == 1;
    return res;
}

//ATOM

predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

//IMPL DivMod

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
    /* code modified by LLM (iteration 1): Initialize quotient and remainder properly */
    quotient := "0";
    remainder := dividend;
    
    var one := "1";
    
    /* code modified by LLM (iteration 1): Fixed loop with proper termination and invariants */
    while Str2Int(remainder) >= Str2Int(divisor)
        invariant ValidBitString(quotient) && ValidBitString(remainder)
        invariant ValidBitString(one) && Str2Int(one) == 1
        invariant Str2Int(quotient) * Str2Int(divisor) + Str2Int(remainder) == Str2Int(dividend)
        invariant Str2Int(remainder) >= 0
        decreases Str2Int(remainder)
    {
        remainder := Sub(remainder, divisor);
        quotient := Add(quotient, one);
    }
}

/* code modified by LLM (iteration 1): Added helper method for addition with proper string handling */
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
    /* code modified by LLM (iteration 1): Handle zero cases first */
    if Str2Int(s1) == 0 {
        res := s2;
        return;
    }
    if Str2Int(s2) == 0 {
        res := s1;
        return;
    }
    
    /* code modified by LLM (iteration 1): Implement binary addition with carry using proper string operations */
    var result := "";
    var carry := 0;
    var maxLen := if |s1| > |s2| then |s1| else |s2|
    var i := 0;
    
    /* code modified by LLM (iteration 1): Pad strings to same length for easier processing */
    var padded_s1 := PadLeft(s1, maxLen);
    var padded_s2 := PadLeft(s2, maxLen);
    
    while i < maxLen || carry > 0
        invariant 0 <= i <= maxLen
        invariant 0 <= carry <= 1
        invariant ValidBitString(result)
        invariant ValidBitString(padded_s1) && ValidBitString(padded_s2)
        invariant |padded_s1| == maxLen && |padded_s2| == maxLen
        decreases maxLen - i + carry
    {
        var bit1 := if i < |padded_s1| then (if padded_s1[|padded_s1| - 1 - i] == '1' then 1 else 0) else 0;
        var bit2 := if i < |padded_s2| then (if padded_s2[|padded_s2| - 1 - i] == '1' then 1 else 0) else 0;
        var sum := bit1 + bit2 + carry;
        
        var newBit := if sum % 2 == 1 then '1' else '0';
        result := [newBit] + result;
        carry := sum / 2;
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): Handle empty result case */
    if result == "" {
        res := "0";
    } else {
        res := result;
    }
}

/* code modified by LLM (iteration 1): Added helper method to pad strings with leading zeros */
method PadLeft(s: string, targetLength: int) returns (result: string)
  requires ValidBitString(s)
  requires targetLength >= |s|
  ensures ValidBitString(result)
  ensures |result| == targetLength
  ensures Str2Int(result) == Str2Int(s)
{
    result := s;
    var zerosNeeded := targetLength - |s|;
    var i := 0;
    
    while i < zerosNeeded
        invariant 0 <= i <= zerosNeeded
        invariant ValidBitString(result)
        invariant |result| == |s| + i
        invariant Str2Int(result) == Str2Int(s)
        decreases zerosNeeded - i
    {
        result := "0" + result;
        i := i + 1;
    }
}