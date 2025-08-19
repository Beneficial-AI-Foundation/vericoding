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

/* code modified by LLM (iteration 1): Simplified AddOne implementation with basic logic */
method AddOne(s: string) returns (res: string)
  requires ValidBitString(s)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) + 1
{
    if |s| == 0 {
        return "1";
    }
    
    /* code modified by LLM (iteration 1): Recursive approach for adding one */
    if s[|s|-1] == '0' {
        // Last bit is 0, just change it to 1
        res := s[0..|s|-1] + "1";
    } else {
        // Last bit is 1, change to 0 and carry
        var prefix := AddOne(s[0..|s|-1]);
        res := prefix + "0";
    }
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
    quotient := "";
    remainder := dividend;
    
    /* code modified by LLM (iteration 1): Initialize quotient to empty string and handle empty case */
    if |dividend| == 0 || Str2Int(dividend) == 0 {
        quotient := "0";
        remainder := "";
        return;
    }
    
    quotient := "0";
    
    /* code modified by LLM (iteration 1): Fixed loop with proper invariants */
    while Str2Int(remainder) >= Str2Int(divisor)
        invariant ValidBitString(quotient) && ValidBitString(remainder)
        invariant Str2Int(quotient) * Str2Int(divisor) + Str2Int(remainder) == Str2Int(dividend)
        decreases Str2Int(remainder)
    {
        remainder := Sub(remainder, divisor);
        quotient := AddOne(quotient);
    }
}