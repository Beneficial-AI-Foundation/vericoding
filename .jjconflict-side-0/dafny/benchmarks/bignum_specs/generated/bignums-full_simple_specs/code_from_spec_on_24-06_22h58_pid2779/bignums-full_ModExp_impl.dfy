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

predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

//IMPL ModExp

/* code modified by LLM (iteration 1): Added helper method for subtracting one */
method SubtractOne(s: string) returns (result: string)
  requires ValidBitString(s)
  requires Str2Int(s) > 0
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(s) - 1
{
    result := "";
    if |s| == 0 {
        return;
    }
    
    /* code modified by LLM (iteration 1): Fixed implementation to handle borrowing correctly */
    var bits: seq<char> := [];
    var i := |s| - 1;
    var borrow := true;
    
    while i >= 0
      invariant -1 <= i < |s|
      invariant ValidBitString(seq(bits))
      decreases i
    {
        var current_bit := s[i];
        var new_bit: char;
        
        if borrow {
            if current_bit == '1' {
                new_bit := '0';
                borrow := false;
            } else {
                new_bit := '1';
            }
        } else {
            new_bit := current_bit;
        }
        
        bits := [new_bit] + bits;
        i := i - 1;
    }
    
    result := seq(bits);
}

/* code modified by LLM (iteration 1): Added helper method for checking if string represents zero */
method IsZero(s: string) returns (is_zero: bool)
  requires ValidBitString(s)
  ensures is_zero <==> Str2Int(s) == 0
{
    if |s| == 0 {
        is_zero := true;
        return;
    }
    
    var i := 0;
    is_zero := true;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant is_zero ==> forall j | 0 <= j < i :: s[j] == '0'
      decreases |s| - i
    {
        if s[i] == '1' {
            is_zero := false;
            return;
        }
        i := i + 1;
    }
}

/* code modified by LLM (iteration 1): Added helper method for integer division by 2 in string representation */
method DivideByTwo(s: string) returns (result: string)
  requires ValidBitString(s)
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(s) / 2
{
    if |s| == 0 {
        result := "";
        return;
    }
    
    if |s| == 1 {
        result := "";
        return;
    }
    
    /* code modified by LLM (iteration 1): Right shift by removing last bit */
    result := s[0..|s|-1];
}

// computes (s1^s2) % s3 for bitstrings s1,s2,s3
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1)
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases Str2Int(sy)
{
    /* code modified by LLM (iteration 1): Handle base case when sy represents 0 */
    var sy_is_zero := IsZero(sy);
    if sy_is_zero {
        var one := "1";
        var quotient, remainder := DivMod(one, sz);
        res := remainder;
        return;
    }
    
    /* code modified by LLM (iteration 1): Handle base case when sy represents 1 */
    if |sy| == 1 && sy[0] == '1' {
        var quotient, remainder := DivMod(sx, sz);
        res := remainder;
        return;
    }
    
    /* code modified by LLM (iteration 1): Use binary exponentiation approach */
    if sy[|sy|-1] == '0' {
        // sy is even: (sx^sy) % sz = ((sx^(sy/2))^2) % sz
        var half_exp_input := DivideByTwo(sy);
        var half_exp := ModExp(sx, half_exp_input, sz);
        var squared := Mul(half_exp, half_exp);
        var final_quotient, final_remainder := DivMod(squared, sz);
        res := final_remainder;
    } else {
        // sy is odd: (sx^sy) % sz = (sx * (sx^(sy-1))) % sz
        var sy_minus_one := SubtractOne(sy);
        var exp_result := ModExp(sx, sy_minus_one, sz);
        var sx_quotient, sx_mod := DivMod(sx, sz);
        var temp := Mul(sx_mod, exp_result);
        var final_quotient, final_remainder := DivMod(temp, sz);
        res := final_remainder;
    }
}