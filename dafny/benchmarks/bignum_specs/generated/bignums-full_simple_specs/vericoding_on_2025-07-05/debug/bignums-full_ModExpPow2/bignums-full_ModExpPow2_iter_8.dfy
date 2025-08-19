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

/* code modified by LLM (iteration 1): Added helper lemmas for modular exponentiation properties */
lemma ModularArithmetic(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma ExpIntProperty(base: nat, exp1: nat, exp2: nat)
  ensures Exp_int(base, exp1 + exp2) == Exp_int(base, exp1) * Exp_int(base, exp2)
{
  reveal Exp_int;
  if exp2 == 0 {
    assert exp1 + exp2 == exp1;
  } else {
    ExpIntProperty(base, exp1, exp2 - 1);
  }
}

lemma PowerOfTwoProperty(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n - 1)
{
  reveal Exp_int;
}

/* code modified by LLM (iteration 1): Helper lemma for power of 2 doubling property */
lemma PowerOfTwoDoubling(n: nat)
  ensures Exp_int(2, n) + Exp_int(2, n) == Exp_int(2, n + 1)
{
  reveal Exp_int;
  if n == 0 {
    assert Exp_int(2, 0) == 1;
    assert Exp_int(2, 1) == 2;
  } else {
    PowerOfTwoDoubling(n - 1);
  }
}

/* code modified by LLM (iteration 1): Helper lemma for exponentiation with power of 2 exponents */
lemma ExpWithPowerOfTwoExponent(base: nat, n: nat)
  ensures Exp_int(base, Exp_int(2, n)) == Exp_int(Exp_int(base, Exp_int(2, n-1)), Exp_int(2, n-1))
  requires n > 0
{
  reveal Exp_int;
  PowerOfTwoDoubling(n-1);
  ExpIntProperty(base, Exp_int(2, n-1), Exp_int(2, n-1));
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
  /* code modified by LLM (iteration 1): Handle base case when sy represents 0 */
  if Str2Int(sy) == 0 {
    res := "1";
    reveal Exp_int;
    return;
  }
  
  /* code modified by LLM (iteration 1): Handle base case when n == 0 */
  if n == 0 {
    reveal Exp_int;
    assert Str2Int(sy) == 1;
    var quotient, remainder := DivMod(sx, sz);
    res := remainder;
    return;
  }
  
  /* code modified by LLM (iteration 1): Create bit string for 2^(n-1) - construct manually */
  var sy_half: string;
  if n == 1 {
    sy_half := "1";
  } else {
    sy_half := "1" + seq(n-1, _ => '0');
  }
  
  /* code modified by LLM (iteration 1): Verify sy_half properties */
  assert ValidBitString(sy_half);
  assert |sy_half| == n;
  
  /* code modified by LLM (iteration 1): Apply power property lemma */
  PowerOfTwoProperty(n);
  reveal Exp_int;
  
  /* code modified by LLM (iteration 1): Prove sy_half represents 2^(n-1) */
  if n == 1 {
    assert Str2Int(sy_half) == 1;
    assert Exp_int(2, 0) == 1;
  } else {
    // For n > 1, sy_half = "1" + (n-1) zeros represents 2^(n-1)
    assert Str2Int(sy_half) == Exp_int(2, n-1);
  }
  
  /* code modified by LLM (iteration 1): Recursive call with proper preconditions */
  var temp_res := ModExpPow2(sx, sy_half, n-1, sz);
  
  /* code modified by LLM (iteration 1): Apply exponentiation property for verification */
  ExpWithPowerOfTwoExponent(Str2Int(sx), n);
  
  /* code modified by LLM (iteration 1): Square the result and take modulo */
  var squared := Mul(temp_res, temp_res);
  var quotient, remainder := DivMod(squared, sz);
  res := remainder;
  
  /* code modified by LLM (iteration 1): Apply modular arithmetic properties for verification */
  ModularArithmetic(Str2Int(temp_res), Str2Int(temp_res), Str2Int(sz));
}