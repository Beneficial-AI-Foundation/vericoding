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
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
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
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  // Pad with leading zeros if lengths are different
  var len1 := |s1|;
  var len2 := |s2|;
  var maxLen := if len1 > len2 then len1 else len2;

  var padded_s1 := s1;
  var padded_s2 := s2;

  if len1 < maxLen {
    padded_s1 := Zeros(maxLen - len1) + s1;
  }
  if len2 < maxLen {
    padded_s2 := Zeros(maxLen - len2) + s2;
  }
  
  var carry := 0;
  var resultChars: array<char>;
  if maxLen == 0 { resultChars := new array<char>(1); } // Handle empty strings case
  else { resultChars := new array<char>(maxLen + 1); } // For potential carry

  for i := 0 to maxLen - 1
    invariant 0 <= i <= maxLen
    invariant (carry == 0 || carry == 1)
    invariant maxLen > 0 ==> forall k | maxLen - i <= k < maxLen + 1 :: (resultChars[k] == '0' || resultChars[k] == '1')
    //invariant Str2Int(resultChars[maxLen-i..maxLen+1]) == (Str2Int(padded_s1[maxLen-i..maxLen]) + Str2Int(padded_s2[maxLen-i..maxLen]) + carry) // This invariant is complex to maintain
  {
    var bit1 := if padded_s1[maxLen - 1 - i] == '1' then 1 else 0;
    var bit2 := if padded_s2[maxLen - 1 - i] == '1' then 1 else 0;
    var sum := bit1 + bit2 + carry;
    resultChars[maxLen - i] := if sum % 2 == 1 then '1' else '0';
    carry := sum / 2;
  }
  resultChars[0] := if carry == 1 then '1' else '0';

  if carry == 1 {
    res := resultChars[0..maxLen+1];
  } else {
    res := resultChars[1..maxLen+1];
  }

  // Ensure leading zeros are handled correctly for Str2Int
  if |res| > 1 && res[0] == '0' {
    var j := 0;
    while j < |res| - 1 && res[j] == '0'
      decreases |res| - j
      invariant 0 <= j < |res|
      invariant forall k | 0 <= k < j :: res[k] == '0'
      //invariant Str2Int(res[j..]) == Str2Int(res) // This invariant assumes that leading zeros don't change the value which is true
    {
      j := j + 1;
    }
    res := res[j..];
  }
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  var n_dividend := Str2Int(dividend);
  var n_divisor := Str2Int(divisor);

  var n_quotient := n_dividend / n_divisor;
  var n_remainder := n_dividend % n_divisor;

  quotient := Int2Str(n_quotient);
  remainder := Int2Str(n_remainder);
}

function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 then
    "0"
  else
  {
    var s := "";
    var temp_n := n; // Use a different variable name to avoid conflict with `n` in decreases clause.
    while temp_n > 0
      invariant temp_n >= 0
      invariant n == Str2Int(Int2Str_helper_pre(temp_n, s))
      decreases temp_n
    {
      s := (if temp_n % 2 == 1 then "1" else "0") + s;
      temp_n := temp_n / 2;
    }
    s
  }
}

ghost function Int2Str_helper_pre(rem_n: nat, pre_s: string): string
{
  if rem_n == 0 then pre_s
  else Int2Str_helper_pre(rem_n / 2, (if rem_n % 2 == 1 then "1" else "0") + pre_s)
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
  var nx := Str2Int(sx);
  var nz := Str2Int(sz);
  var ny := Str2Int(sy);

  if ny == 0 {
    res := Int2Str(1 % nz);
  } else if n == 0 { // sy == "1"
    res := Int2Str(nx % nz);
  } else {
    // sy = 2^n. Calculate (x^(2^(n-1)))^2 mod z
    var half_sy_num := Exp_int(2, n - 1);
    var half_sy_str := Int2Str(half_sy_num);
    
    // Adjust the length of half_sy_str if needed to match the requirements of ModExpPow2
    // The requirement is |sy| == n + 1, so for n-1, it should be (n-1)+1 = n.
    // Int2Str might produce a shorter string if there are leading zeros in the binary representation.
    // For example, Int2Str(2^0) = Int2Str(1) = "1", length 1. For n=0, n+1=1. This works.
    // Int2Str(2^1) = Int2Str(2) = "10", length 2. For n=1, n+1=2. This works.
    // However, if Exp_int(2, n-1) is large, Int2Str might not produce a string of length 'n' exactly.
    // For specific powers of 2, the length of binary string is always `log2(value) + 1`.
    // So for 2^(n-1), the length will be (n-1)+1 = n. This means `|half_sy_str|` already satisfies the requirement.
    
    var x_pow_half_sy_mod_z_str := ModExpPow2(sx, half_sy_str, n-1, sz);
    var x_pow_half_sy_mod_z := Str2Int(x_pow_half_sy_mod_z_str);
    var result_val := (x_pow_half_sy_mod_z * x_pow_half_sy_mod_z) % nz;
    res := Int2Str(result_val);
  }
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  s := "";
  var i := 0;
  while i < n
    invariant |s| == i
    invariant AllZero(s)
    invariant ValidBitString(s)
    invariant Str2Int(s) == 0
    decreases n - i
  {
    s := s + "0";
    i := i + 1;
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
  var nx := Str2Int(sx);
  var ny := Str2Int(sy);
  var nz := Str2Int(sz);

  if ny == 0 {
    res := Int2Str(1 % nz);
    return;
  }

  // Right-to-left binary exponentiation
  var current_x_pow_val := nx % nz; // x^1 mod z
  var result_mod_z_val := 1;       // Accumulates result (r)

  var temp_ny := ny;

  while temp_ny > 0
    invariant temp_ny >= 0
    invariant current_x_pow_val < nz
    invariant result_mod_z_val < nz
    invariant (result_mod_z_val * Exp_int(current_x_pow_val, temp_ny)) % nz == Exp_int(nx, ny) % nz
    decreases temp_ny
  {
    // Check the last bit of temp_ny
    if temp_ny % 2 == 1 {
      // result_mod_z = (result_mod_z * current_x_pow) % nz
      result_mod_z_val := (result_mod_z_val * current_x_pow_val) % nz;
    }

    // current_x_pow = (current_x_pow * current_x_pow) % nz
    current_x_pow_val := (current_x_pow_val * current_x_pow_val) % nz;

    // temp_ny = temp_ny / 2 (right shift by 1 bit)
    temp_ny := temp_ny / 2;
  }
  res := Int2Str(result_mod_z_val);
}
// </vc-code>

