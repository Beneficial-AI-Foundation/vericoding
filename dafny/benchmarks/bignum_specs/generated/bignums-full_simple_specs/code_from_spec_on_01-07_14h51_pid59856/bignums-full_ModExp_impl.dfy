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


//IMPL ModExp

/* code modified by LLM (iteration 1): Added missing AllZero predicate definition */
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

/* code modified by LLM (iteration 1): Added helper method to check if string represents zero */
method IsZero(s: string) returns (isZero: bool)
  requires ValidBitString(s)
  ensures isZero <==> Str2Int(s) == 0
{
  isZero := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant isZero <==> (forall j | 0 <= j < i :: s[j] == '0')
  {
    if s[i] == '1' {
      isZero := false;
      return;
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 1): Added helper method to check if string represents one */
method IsOne(s: string) returns (isOne: bool)
  requires ValidBitString(s)
  ensures isOne <==> Str2Int(s) == 1
{
  if |s| == 0 {
    isOne := false;
    return;
  }
  
  if |s| == 1 && s[0] == '1' {
    isOne := true;
    return;
  }
  
  if |s| > 1 {
    var leadingZero := true;
    var i := 0;
    while i < |s| - 1
      invariant 0 <= i <= |s| - 1
      invariant leadingZero <==> (forall j | 0 <= j < i :: s[j] == '0')
    {
      if s[i] == '1' {
        leadingZero := false;
      }
      i := i + 1;
    }
    isOne := leadingZero && s[|s| - 1] == '1';
  } else {
    isOne := false;
  }
}

/* code modified by LLM (iteration 1): Added helper method to create string "1" */
method One() returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == 1
{
  s := "1";
}

/* code modified by LLM (iteration 1): Added helper method to create string "10" (binary 2) */
method Two() returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == 2
{
  s := "10";
}

/* code modified by LLM (iteration 1): Added helper lemma for exponentiation base case */
lemma ExpIntBase(x: nat)
  ensures Exp_int(x, 0) == 1
{
  reveal Exp_int;
}

/* code modified by LLM (iteration 1): Added helper lemma for exponentiation properties */
lemma ExpIntStep(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
  reveal Exp_int;
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
    var syIsZero := IsZero(sy);
    if syIsZero {
        ExpIntBase(Str2Int(sx));
        var one := One();
        var _, remainder := DivMod(one, sz);
        res := remainder;
        return;
    }
    
    /* code modified by LLM (iteration 1): Handle base case when sy represents 1 */
    var syIsOne := IsOne(sy);
    if syIsOne {
        var _, remainder := DivMod(sx, sz);
        res := remainder;
        return;
    }
    
    /* code modified by LLM (iteration 1): Use binary exponentiation algorithm */
    var two := Two();
    var quotient, remainder := DivMod(sy, two); // sy / 2
    var remainderIsZero := IsZero(remainder);
    var isEven := remainderIsZero;
    
    // Recursive call with sy/2
    var halfRes := ModExp(sx, quotient, sz);
    
    // Square the result: (sx^(sy/2))^2
    var squared := Mul(halfRes, halfRes);
    var _, squaredMod := DivMod(squared, sz);
    
    if isEven {
        res := squaredMod;
    } else {
        // If sy is odd: sx^sy = sx * (sx^(sy/2))^2
        var temp := Mul(sx, squaredMod);
        var _, finalMod := DivMod(temp, sz);
        res := finalMod;
    }
}