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
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2int(divisor)
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


//IMPL ModExpPow2

/* code modified by LLM (iteration 1): Added helper function to construct power of 2 strings */
function PowerOf2String(n: nat): string
{
  if n == 0 then "1" else "1" + seq(n, i => '0')
}

/* code modified by LLM (iteration 1): Added lemmas for power of 2 string properties */
lemma PowerOf2StringValid(n: nat)
  ensures ValidBitString(PowerOf2String(n))
{
  var s := PowerOf2String(n);
  if n == 0 {
    assert s == "1";
    assert ValidBitString(s);
  } else {
    assert s == "1" + seq(n, i => '0');
    assert ValidBitString(s);
  }
}

lemma PowerOf2StringValue(n: nat)
  requires ValidBitString(PowerOf2String(n))
  ensures Str2Int(PowerOf2String(n)) == Exp_int(2, n)
{
  reveal Exp_int;
  var s := PowerOf2String(n);
  if n == 0 {
    assert s == "1";
    assert Str2Int(s) == 1;
    assert Exp_int(2, 0) == 1;
  }
}

/* code modified by LLM (iteration 1): Added lemma for exponentiation doubling property */
lemma ExpDoublingLemma(base: nat, exp: nat)
  ensures Exp_int(base, 2 * exp) == Exp_int(Exp_int(base, exp), 2)
{
  reveal Exp_int;
}

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
  if Str2Int(sy) == 0 {
    /* code modified by LLM (iteration 1): Handle base case when sy represents 0 */
    res := "1";
    reveal Exp_int;
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert Str2Int(res) == 1;
  } else if n == 0 {
    /* code modified by LLM (iteration 1): Handle case when n=0, so sy = 2^0 = 1 */
    reveal Exp_int;
    assert Str2Int(sy) == Exp_int(2, 0) == 1;
    var quotient, remainder := DivMod(sx, sz);
    res := remainder;
    assert Str2Int(res) == Str2Int(sx) % Str2Int(sz);
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
  } else {
    /* code modified by LLM (iteration 1): Handle recursive case with proper construction */
    // sy represents 2^n where n > 0
    // We want to compute sx^(2^n) = (sx^(2^(n-1)))^2
    
    var half_sy := PowerOf2String(n-1);
    PowerOf2StringValid(n-1);
    PowerOf2StringValue(n-1);
    
    assert ValidBitString(half_sy);
    assert Str2Int(half_sy) == Exp_int(2, n-1);
    assert |half_sy| == n;  // Since PowerOf2String(n-1) has length n when n > 0
    
    // Recursive call
    var temp_res := ModExpPow2(sx, half_sy, n-1, sz);
    
    // Square the result: (sx^(2^(n-1)))^2 = sx^(2^n)
    var squared := Mul(temp_res, temp_res);
    
    // Take modulo
    var quotient, remainder := DivMod(squared, sz);
    res := remainder;
    
    // Proof obligations
    reveal Exp_int;
    ExpDoublingLemma(Str2Int(sx), Exp_int(2, n-1));
    assert Str2Int(sy) == Exp_int(2, n);
    assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
  }
}