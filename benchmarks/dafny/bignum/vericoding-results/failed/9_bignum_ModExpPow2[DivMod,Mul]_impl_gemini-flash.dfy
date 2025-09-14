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
function Pow2N(n: nat): nat
  ensures Pow2N(n) == Exp_int(2, n)
{
  Exp_int(2, n)
}
function CreateBitStringFromNat(value: nat): string
  ensures ValidBitString(CreateBitStringFromNat(value))
  ensures Str2Int(CreateBitStringFromNat(value)) == value
{
  if value == 0 then
    "0"
  else if value == 1 then
    "1"
  else
  (
    var s_remainder := if value % 2 == 1 then "1" else "0";
    var s_prefix_val := value / 2;
    var s_prefix := CreateBitStringFromNat(s_prefix_val);
    s_prefix + s_remainder
  )
}

// Helper method to perform DivMod and return remainder
method GetRemainder(dividend_str: string, divisor_str: string) returns (remainder: string)
  requires ValidBitString(dividend_str) && ValidBitString(divisor_str)
  requires Str2Int(divisor_str) > 0
  ensures ValidBitString(remainder)
  ensures Str2Int(remainder) == Str2Int(dividend_str) % Str2Int(divisor_str)
{
  var quotient_str: string;
  var r: string;
  (quotient_str, r) := DivMod(dividend_str, divisor_str);
  remainder := r;
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

  if y_int == 0 {
    res := "1"; // x^0 = 1
  } else {
    // If y_int is a power of 2, say 2^n
    // We need to implement x^(2^n) % z
    // This can be done by repeated squaring:
    // x^(2^n) = x^2 * x^2 * ... (n times) modulus z
    // x^(2^n) = (x^(2^(n-1)))^2

    // Base case for recursion, when sy becomes "1" (2^0)
    if n == 0 { // sy is "1" here
      res := GetRemainder(sx, sz);
    } else {
      // Calculate temp = x^(2^(n-1)) % z
      // To pass the correct sy for the recursive call, it should represent 2^(n-1)
      // Since |sy| == n+1, we need a string of length n for the next call
      // The sy for the recursive call should be "1" followed by n-1 zeros,
      // which corresponds to Str2Int("1" + "0" * (n-1)) = 2^(n-1).
      var sy_half_nat := Exp_int(2, n - 1);
      var sy_half := CreateBitStringFromNat(sy_half_nat);

      // Add padding to sy_half to match the expected length for the recursive call.
      // The recursive call expects `|sy_half| == (n-1)+1`, i.e., `|sy_half| == n`.
      // `CreateBitStringFromNat` does not guarantee a specific length, only the value.
      // So, if `sy_half_nat` is 0, it creates "0" (length 1). If `sy_half_nat` is a power
      // of 2 (2^(k)), it creates "1" followed by `k` zeros (length k+1).
      // Here, `sy_half_nat` is 2^(n-1), so `CreateBitStringFromNat` will produce a string of length `(n-1)+1 = n`.
      // Therefore, no additional padding/manipulation is needed for `sy_half`.

      var temp_res := ModExpPow2(sx, sy_half, n - 1, sz);

      var squared_string := Mul(temp_res, temp_res);

      res := GetRemainder(squared_string, sz);
    }
  }
}
// </vc-code>

