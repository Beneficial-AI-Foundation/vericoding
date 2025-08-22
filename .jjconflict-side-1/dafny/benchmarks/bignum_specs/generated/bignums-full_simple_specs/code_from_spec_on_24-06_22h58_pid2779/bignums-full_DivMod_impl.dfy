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
    quotient := "0";
    remainder := dividend;
    
    var cmp := Compare(remainder, divisor);
    while cmp >= 0
        invariant ValidBitString(quotient) && ValidBitString(remainder)
        invariant Str2Int(remainder) >= 0
        invariant Str2Int(quotient) * Str2Int(divisor) + Str2Int(remainder) == Str2Int(dividend)
        decreases Str2Int(remainder)
    {
        var temp := Sub(remainder, divisor);
        remainder := temp;
        
        // Add 1 to quotient (simple increment)
        var carry := 1;
        var newQuotient := "";
        var i := |quotient|;
        
        while i > 0 && carry > 0
            invariant 0 <= i <= |quotient|
            invariant carry == 0 || carry == 1
            invariant ValidBitString(newQuotient)
        {
            i := i - 1;
            if quotient[i] == '0' {
                newQuotient := "1" + newQuotient;
                carry := 0;
            } else {
                newQuotient := "0" + newQuotient;
                carry := 1;
            }
        }
        
        while i > 0
            invariant 0 <= i <= |quotient|
            invariant ValidBitString(newQuotient)
        {
            i := i - 1;
            newQuotient := quotient[i..i+1] + newQuotient;
        }
        
        if carry > 0 {
            newQuotient := "1" + newQuotient;
        }
        
        quotient := newQuotient;
        cmp := Compare(remainder, divisor);
    }
}