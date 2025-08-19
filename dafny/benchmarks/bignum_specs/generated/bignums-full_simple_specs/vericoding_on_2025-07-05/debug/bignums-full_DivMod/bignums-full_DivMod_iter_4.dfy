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
    
    /* code modified by LLM (iteration 1): Fixed loop with proper termination condition */
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
        quotient := Add(quotient, one);
    }
}

/* code modified by LLM (iteration 1): Added helper method for addition */
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
    /* code modified by LLM (iteration 1): Simple implementation using binary addition */
    var n1 := Str2Int(s1);
    var n2 := Str2Int(s2);
    var sum := n1 + n2;
    
    /* code modified by LLM (iteration 1): Convert sum back to binary string */
    if sum == 0 {
        res := "0";
        return;
    }
    
    res := "";
    var temp := sum;
    while temp > 0
        invariant temp >= 0
        invariant ValidBitString(res)
        decreases temp
    {
        if temp % 2 == 1 {
            res := "1" + res;
        } else {
            res := "0" + res;
        }
        temp := temp / 2;
    }
    
    /* code modified by LLM (iteration 1): Ensure result is valid */
    if |res| == 0 {
        res := "0";
    }
}

/* code modified by LLM (iteration 1): Added lemma to help with ValidBitString proof */
lemma ValidBitStringConcat(c: char, s: string)
  requires c == '0' || c == '1'
  requires ValidBitString(s)
  ensures ValidBitString([c] + s)
{
    var result := [c] + s;
    forall i | 0 <= i < |result|
        ensures result[i] == '0' || result[i] == '1'
    {
        if i == 0 {
            assert result[i] == c;
        } else {
            assert result[i] == s[i-1];
        }
    }
}