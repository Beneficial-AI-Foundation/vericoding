//ATOM

// computes (sx^sy) % sz for bitstrings sx,sy,sz when str2int(sy) == 2^n
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
    res := "";
    assume ValidBitString(res);
    assume Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    return res;
}


//ATOM


// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}


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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
    s := "";
    assume |s| == n;
    assume ValidBitString(s);
    assume Str2Int(s) == 0;
    assume AllZero(s);
    return s;
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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
    quotient := "";
    remainder := "";
    assume ValidBitString(quotient) && ValidBitString(remainder);
    assume Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor);
    assume Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor);
    return quotient, remainder;
}


//ATOM



// ----------------------------------------------------
// string-based multiplication
//    No direct use of Str2Int/Int2Str
// ----------------------------------------------------
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
    assume ValidBitString(res);
    assume Str2Int(res) == Str2Int(s1) * Str2Int(s2);
}


//ATOM

predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}


//ATOM

predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}


//IMPL ModExp

// computes (s1^s2) % s3 for bitstrings s1,s2,s3
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1)
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases |sy|
{
    /* code modified by LLM (iteration 1): Handle base case when sy represents 0 */
    if AllZero(sy) {
        res := "1";
        return;
    }
    
    /* code modified by LLM (iteration 1): Handle base case when sy == "1" */
    if sy == "1" {
        var _, remainder := DivMod(sx, sz);
        res := remainder;
        return;
    }
    
    /* code modified by LLM (iteration 1): Implement binary exponentiation using bit manipulation */
    var is_odd: bool := sy[|sy|-1] == '1';
    
    // Create sy_div2 by right-shifting sy (divide by 2)
    var sy_div2: string;
    if |sy| == 1 {
        sy_div2 := "0";
    } else {
        sy_div2 := sy[0..|sy|-1];
        /* code modified by LLM (iteration 1): Ensure sy_div2 is not empty */
        if sy_div2 == "" {
            sy_div2 := "0";
        }
    }
    
    /* code modified by LLM (iteration 1): Ensure proper termination by checking if we've reduced the problem */
    if AllZero(sy_div2) {
        // sy was of the form "1" (handled above) or "10...0" 
        // For "10...0", we need sx^(2^k) where k = |sy|-1
        var temp := sx;
        var remaining_bits := |sy| - 1;
        
        /* code modified by LLM (iteration 1): Repeated squaring with proper invariants */
        while remaining_bits > 0
            decreases remaining_bits
            invariant ValidBitString(temp)
            invariant remaining_bits >= 0
        {
            var temp_squared := Mul(temp, temp);
            var _, temp_mod := DivMod(temp_squared, sz);
            temp := temp_mod;
            remaining_bits := remaining_bits - 1;
        }
        res := temp;
        return;
    }
    
    /* code modified by LLM (iteration 1): Recursive call with guaranteed smaller input */
    var temp := ModExp(sx, sy_div2, sz);
    
    /* code modified by LLM (iteration 1): Square the result */
    var temp_squared := Mul(temp, temp);
    var _, temp_squared_mod := DivMod(temp_squared, sz);
    
    if is_odd {
        /* code modified by LLM (iteration 1): Multiply by sx for odd exponent */
        var temp_times_sx := Mul(temp_squared_mod, sx);
        var _, final_mod := DivMod(temp_times_sx, sz);
        res := final_mod;
    } else {
        /* code modified by LLM (iteration 1): Even exponent case */
        res := temp_squared_mod;
    }
}