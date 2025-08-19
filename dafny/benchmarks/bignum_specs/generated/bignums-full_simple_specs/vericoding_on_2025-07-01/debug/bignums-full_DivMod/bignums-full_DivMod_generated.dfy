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
    if |dividend| == 0 {
        quotient := "0";
        remainder := "0";
        return;
    }
    
    var cmp := Compare(dividend, divisor);
    if cmp == -1 {
        // dividend < divisor
        quotient := "0";
        remainder := dividend;
        return;
    }
    
    if cmp == 0 {
        // dividend == divisor
        quotient := "1";
        remainder := "0";
        return;
    }
    
    // Implement long division
    quotient := "";
    remainder := "0";
    
    var i := 0;
    while i < |dividend|
        invariant 0 <= i <= |dividend|
        invariant ValidBitString(quotient)
        invariant ValidBitString(remainder)
        invariant Str2Int(remainder) < Str2Int(divisor) || i == 0
    {
        // Shift remainder left and add next bit
        remainder := remainder + [dividend[i]];
        
        // Check if we can subtract divisor
        var cmpResult := Compare(remainder, divisor);
        if cmpResult >= 0 {
            quotient := quotient + "1";
            remainder := Sub(remainder, divisor);
        } else {
            quotient := quotient + "0";
        }
        
        i := i + 1;
    }
    
    // Handle empty quotient
    if |quotient| == 0 {
        quotient := "0";
    }
    
    // Handle empty remainder
    if |remainder| == 0 {
        remainder := "0";
    }
}