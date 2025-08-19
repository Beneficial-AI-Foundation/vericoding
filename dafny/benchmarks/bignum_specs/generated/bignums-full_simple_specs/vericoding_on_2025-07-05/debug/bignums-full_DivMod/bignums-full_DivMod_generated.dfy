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
    
    var one := "1";
    
    while true
        invariant ValidBitString(quotient) && ValidBitString(remainder)
        invariant Str2Int(quotient) * Str2Int(divisor) + Str2Int(remainder) == Str2Int(dividend)
        invariant Str2Int(remainder) >= 0
        decreases Str2Int(remainder)
    {
        var cmp := Compare(remainder, divisor);
        if cmp == -1 {
            break;
        }
        
        remainder := Sub(remainder, divisor);
        
        var newQuotient := Add(quotient, one);
        quotient := newQuotient;
    }
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
    res := "";
    var carry := 0;
    var i := 0;
    var len1 := |s1|;
    var len2 := |s2|;
    var maxLen := if len1 > len2 then len1 else len2;
    
    while i < maxLen || carry > 0
        invariant 0 <= i <= maxLen + 1
        invariant ValidBitString(res)
        invariant carry == 0 || carry == 1
        decreases maxLen + 1 - i + carry
    {
        var bit1 := if i < len1 then (if s1[len1 - 1 - i] == '1' then 1 else 0) else 0;
        var bit2 := if i < len2 then (if s2[len2 - 1 - i] == '1' then 1 else 0) else 0;
        
        var sum := bit1 + bit2 + carry;
        var resultBit := if sum % 2 == 1 then '1' else '0';
        carry := sum / 2;
        
        res := [resultBit] + res;
        i := i + 1;
    }
    
    if |res| == 0 {
        res := "0";
    }
}