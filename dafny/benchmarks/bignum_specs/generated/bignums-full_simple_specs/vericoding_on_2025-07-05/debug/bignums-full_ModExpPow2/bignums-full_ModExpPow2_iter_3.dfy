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


//IMPL ModExpPow2

/* code modified by LLM (iteration 1): Added helper lemma and fixed the implementation to properly handle all cases with correct mathematical reasoning */
lemma PowerOfTwoProperty(n: nat)
  ensures n > 0 ==> Exp_int(2, n) == 2 * Exp_int(2, n-1)
{
  if n > 0 {
    reveal Exp_int;
  }
}

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
  /* code modified by LLM (iteration 1): Added proper case handling for sy == 0 */
  if Str2Int(sy) == 0 {
    // sx^0 = 1, so result is 1 % sz
    res := "1";
    reveal Exp_int;
    return;
  }
  
  if n == 0 {
    // sy = 2^0 = 1, so sx^sy = sx^1 = sx
    reveal Exp_int;
    var temp_quotient, temp_remainder := DivMod(sx, sz);
    res := temp_remainder;
    return;
  }
  
  // sy = 2^n where n > 0
  // sx^(2^n) = (sx^(2^(n-1)))^2
  
  /* code modified by LLM (iteration 1): Construct proper bit string for 2^(n-1) with verification */
  var sy_half := "1";
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |sy_half| == i + 1
    invariant ValidBitString(sy_half)
    invariant sy_half[0] == '1'
    invariant forall j | 1 <= j < |sy_half| :: sy_half[j] == '0'
  {
    sy_half := sy_half + "0";
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Added assertion to help Dafny verify the mathematical property */
  assert |sy_half| == n;
  assert ValidBitString(sy_half);
  assert sy_half[0] == '1';
  assert forall j | 1 <= j < |sy_half| :: sy_half[j] == '0';
  
  // The constructed sy_half represents 2^(n-1)
  var temp_res := ModExpPow2(sx, sy_half, n-1, sz);
  
  /* code modified by LLM (iteration 1): Added mathematical reasoning with lemma application */
  PowerOfTwoProperty(n);
  reveal Exp_int;
  
  // Now square the result: (sx^(2^(n-1)))^2 % sz
  var squared := Mul(temp_res, temp_res);
  var temp_quotient, temp_remainder := DivMod(squared, sz);
  res := temp_remainder;
}