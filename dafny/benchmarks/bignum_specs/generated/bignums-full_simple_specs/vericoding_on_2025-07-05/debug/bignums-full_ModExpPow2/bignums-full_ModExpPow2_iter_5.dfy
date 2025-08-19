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

/* code modified by LLM (iteration 1): Added helper lemmas for power of 2 properties */
lemma PowerOfTwoHalving(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n-1)
{
  reveal Exp_int;
}

lemma ModularExponentiationSquaring(base: nat, exp: nat, modulus: nat)
  requires modulus > 1
  requires exp % 2 == 0 && exp > 0
  ensures Exp_int(base, exp) % modulus == (Exp_int(base, exp/2) * Exp_int(base, exp/2)) % modulus
{
  reveal Exp_int;
  var half_exp := exp / 2;
  assert exp == 2 * half_exp;
  ExpIntDoubling(base, half_exp);
}

lemma ExpIntDoubling(base: nat, exp: nat)
  ensures Exp_int(base, 2 * exp) == Exp_int(base, exp) * Exp_int(base, exp)
{
  reveal Exp_int;
  if exp == 0 {
    // base case
  } else {
    ExpIntDoubling(base, exp - 1);
  }
}

/* code modified by LLM (iteration 1): Helper function to create power of 2 bit strings */
function PowerOfTwoBitString(n: nat): string
{
  if n == 0 then "1" else "1" + seq(n, _ => '0')
}

lemma PowerOfTwoBitStringCorrect(n: nat)
  ensures ValidBitString(PowerOfTwoBitString(n))
  ensures |PowerOfTwoBitString(n)| == n + 1
  ensures Str2Int(PowerOfTwoBitString(n)) == Exp_int(2, n)
{
  var s := PowerOfTwoBitString(n);
  if n == 0 {
    reveal Exp_int;
  } else {
    reveal Exp_int;
    PowerOfTwoBitStringHelper(n);
  }
}

lemma PowerOfTwoBitStringHelper(n: nat)
  requires n > 0
  ensures Str2Int(PowerOfTwoBitString(n)) == Exp_int(2, n)
{
  reveal Exp_int;
  // The bit string "1" followed by n zeros represents 2^n
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
  /* code modified by LLM (iteration 1): Handle the case when sy represents 0 */
  if Str2Int(sy) == 0 {
    res := "1";
    reveal Exp_int;
    var quotient, remainder := DivMod(res, sz);
    res := remainder;
    return;
  }
  
  /* code modified by LLM (iteration 1): Base case when n == 0, so sy represents 2^0 = 1 */
  if n == 0 {
    reveal Exp_int;
    // sx^1 % sz = sx % sz
    var quotient, remainder := DivMod(sx, sz);
    res := remainder;
    return;
  }
  
  /* code modified by LLM (iteration 1): Recursive case - use the fact that 2^n = 2 * 2^(n-1) */
  var sy_half := PowerOfTwoBitString(n - 1);
  PowerOfTwoBitStringCorrect(n - 1);
  
  /* code modified by LLM (iteration 1): Apply mathematical property of powers */
  PowerOfTwoHalving(n);
  reveal Exp_int;
  
  /* code modified by LLM (iteration 1): Recursive call to compute sx^(2^(n-1)) % sz */
  var temp_res := ModExpPow2(sx, sy_half, n-1, sz);
  
  /* code modified by LLM (iteration 1): Square the result to get sx^(2^n) % sz */
  var squared := Mul(temp_res, temp_res);
  var quotient, remainder := DivMod(squared, sz);
  res := remainder;
  
  /* code modified by LLM (iteration 1): Mathematical verification using modular arithmetic properties */
  ModularExponentiationSquaring(Str2Int(sx), Exp_int(2, n), Str2Int(sz));
}