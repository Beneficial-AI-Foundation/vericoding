ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Modulo(x: nat, y: nat): nat
  requires y > 0
  ensures 0 <= Modulo(x, y) < y
{
  x % y
}

function Divide(x: nat, y: nat): nat
  requires y > 0
{
  x / y
}

function Power(base: nat, exponent: nat): nat
{
  if exponent == 0 then 1 else base * Power(base, exponent - 1)
}

predicate IsPowerOfTwo(n: nat)
{
  // n must be of type nat to avoid bitwise operation errors.
  n > 0 && ((n as int) & ((n - 1) as int)) == 0
}

// Helper function to convert a natural number to a bit string
function nat2Str(x: nat): string
  ensures ValidBitString(nat2Str(x))
  ensures Str2Int(nat2Str(x)) == x
{
  if x == 0 then
    "0"
  else
    var s := "";
    var temp := x;
    while temp > 0
      invariant temp >= 0
      invariant x == Str2Int(s) * Power(2, |s|) + temp
      // The invariant `x == Str2Int(s) + temp * Power(2, |s|)` was incorrect.
      // It should refer to the value being built from right to left.
      // This new invariant ensures the conversion logic is correct.
      decreasing temp
    {
      s := (if temp % 2 == 1 then "1" else "0") + s;
      temp := temp / 2;
    }
    s
}

// Function to compute (base^exponent) % modulus
// This is a standard modular exponentiation algorithm
function ModExp(base: nat, exponent: nat, modulus: nat): nat
  requires modulus > 1
  decreases exponent
{
  if exponent == 0 then
    1 % modulus
  else if exponent % 2 == 0 then
    var half_exp := ModExp(base, exponent / 2, modulus);
    (half_exp * half_exp) % modulus
  else
    (base * ModExp(base, exponent - 1, modulus)) % modulus
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
    var x_int := Str2Int(sx);
    var y_int := Str2Int(sy);
    var z_int := Str2Int(sz);

    // If y_int is 0, Exp_int(x_int, 0) is 1.
    // So Exp_int(x_int, y_int) % z_int should be 1 % z_int.
    // However, if z_int is 1, 1 % 1 is 0.
    // The spec requires sz > 1, so z_int > 1. Thus 1 % z_int is 1.
    if y_int == 0 {
      res := "1";
    } else {
        // Since sy is a power of 2 (or 0, handled above), Str2Int(sy) = 2^n
        // We need to compute (x_int ^ (2^n)) % z_int
        // This is equivalent to ModExp(x_int, y_int, z_int)
        var result_int := ModExp(x_int, y_int, z_int);
        res := nat2Str(result_int);
    }
}
// </vc-code>

