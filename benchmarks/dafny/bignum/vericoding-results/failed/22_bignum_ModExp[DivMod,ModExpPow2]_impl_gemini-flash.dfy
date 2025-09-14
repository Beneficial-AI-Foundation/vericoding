ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
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
  assume{:axiom} false;
}

// <vc-helpers>
function intToStr(n: nat): string
{
  if n == 0 then "0"
  else intToStrNonZero(n)
}

function intToStrNonZero(n: nat): string
  requires n > 0
  decreases n
{
  if n == 1 then "1"
  else intToStrNonZero(n / 2) + (if n % 2 == 1 then "1" else "0")
}

// Lemma to ensure intToStr produces a valid bit string
lemma IntToStrValidBitString(n: nat)
  ensures ValidBitString(intToStr(n))
{
  if n == 0 {
  } else {
    IntToStrValidBitStringNonZero(n);
  }
}

lemma IntToStrValidBitStringNonZero(n: nat)
  requires n > 0
  ensures ValidBitString(intToStrNonZero(n))
{
  if n == 1 {
  } else {
    IntToStrValidBitStringNonZero(n / 2);
  }
}


// Lemma to show that Str2Int(intToStr(n)) == n for non-negative n
lemma Str2IntIntToStrIdentity(n: nat)
  ensures Str2Int(intToStr(n)) == n
{
  if n == 0 {
  } else {
    Str2IntIntToStrIdentityNonZero(n);
  }
}

lemma Str2IntIntToStrIdentityNonZero(n: nat)
  requires n > 0
  ensures Str2Int(intToStrNonZero(n)) == n
{
  if n == 1 {
  } else {
    // This call is needed to ensure the recursive proof
    Str2IntIntToStrIdentityNonZero(n / 2); 
    IntToStrValidBitStringNonZero(n / 2); // Ensure precondition for recursive call
  }
}


lemma Str2IntLemma(s: string)
  requires ValidBitString(s)
  ensures |s| == 0 ==> Str2Int(s) == 0
  ensures |s| > 0 ==> Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{}

lemma Exp_int_pos_base(x: nat, y: nat)
  requires x > 0
  ensures Exp_int(x, y) > 0
{
  if y == 0 {
  } else {
    Exp_int_pos_base(x, y - 1);
  }
}

lemma Exp_int_monotonic(x: nat, y1: nat, y2: nat)
  requires x > 0
  requires y1 <= y2
  ensures Exp_int(x, y1) <= Exp_int(x, y2)
{
  if y1 == y2 {
    // trivial
  } else if y1 < y2 && y1 == 0 {
    // Exp(x, 0) == 1, Exp_int(x, y2) >= 1
    Exp_int_pos_base(x, y2);
  } else if y1 < y2 {
    Exp_int_monotonic(x, y1, y2 - 1);
  }
}

// Helper method to compute modular exponentiation.
// This method is not ghost as it performs calculations with non-ghost variables.
method ModExp' (x: nat, y: nat, z: nat) returns (res: nat)
  requires z > 1
  decreases y
  ensures res == Exp_int(x, y) % z
{
  if y == 0 {
    res := 1 % z;
  } else if y == 1 {
    res := x % z;
  } else {
    var sy_prime_val := y / 2;
    var sy_lsb_val := y % 2;

    var temp_res := ModExp'(x, sy_prime_val, z);
    
    if sy_lsb_val == 0 {
      res := (temp_res * temp_res) % z;
    } else {
      res := (temp_res * temp_res * (x % z)) % z;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1)
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases |sy|
// </vc-spec>
// <vc-code>
{
    var x_val := Str2Int(sx);
    var y_val := Str2Int(sy);
    var z_val := Str2Int(sz);

    var res_val := ModExp'(x_val, y_val, z_val);

    IntToStrValidBitString(res_val);
    Str2IntIntToStrIdentity(res_val);
    return intToStr(res_val);
}
// </vc-code>

