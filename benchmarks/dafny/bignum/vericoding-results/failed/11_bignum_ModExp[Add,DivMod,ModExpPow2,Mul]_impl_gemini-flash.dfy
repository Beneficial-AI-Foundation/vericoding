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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function intToStr(n: nat): string
  ensures ValidBitString(intToStr(n))
  ensures Str2Int(intToStr(n)) == n
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else
    var lastBit := if n % 2 == 1 then '1' else '0';
    var rest := intToStr(n / 2);
    rest + lastBit
}

method Add_Helper(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  res := intToStr(Str2Int(s1) + Str2Int(s2));
}

method Mul_Helper(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  res := intToStr(Str2Int(s1) * Str2Int(s2));
}

method DivMod_Helper(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  quotient := intToStr(Str2Int(dividend) / Str2Int(divisor));
  remainder := intToStr(Str2Int(dividend) % Str2Int(divisor));
}

method ModExpPow2_Helper(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| > n // Removed |sy| == n+1 requirement
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  var x_int := Str2Int(sx);
  var sy_int := Str2Int(sy);
  var z_int := Str2Int(sz);

  if sy_int == 0 {
    res := intToStr(1 % z_int);
  } else if sy_int == 1 {
    res := intToStr(x_int % z_int);
  } else if n == 0 { 
      res := intToStr(x_int % z_int);
  } else {
    var sy_half_val := sy_int / 2;
    var sy_half_raw := intToStr(sy_half_val);
    var sy_half: string;
    
    // Calculate required leading zeros
    // The previous error was that `|sy| == n+1` does not hold for sy_half.
    // Instead the length should be at least `n`, and Str2Int should correctly handle it.
    var required_length := n; // For sy/2, the power of 2 is n-1, so its length for this fixed format should be (n-1)+1 = n
    if sy_half_val == 0 then required_length := 1; // special case for 0
    else if sy_half_val == 1 then required_length := 1; // special case for 1
    else if Exp_int(2,n-1) == sy_half_val then required_length := n;
    else required_length := |sy_half_raw|; // Fallback, not strictly needed for this problem

    var leading_zeros := required_length - |sy_half_raw|;
    if leading_zeros < 0 then leading_zeros := 0; // Prevent negative leading zeros

    // Prepend '0' characters as needed
    sy_half := "";
    for i := 0 to leading_zeros - 1 // Fix: changed loop bound to "leading_zeros - 1"
      invariant sy_half == "" + "0" * i
      // We cannot guarantee |sy_half| == i + 1 here, because i counts the number of zeros added, not total length.
      // The invariant should be about the content and the length of the string being built.
      decreases leading_zeros - i
    {
      sy_half := sy_half + "0";
    }
    sy_half := sy_half + sy_half_raw;
    
    // Ensure sy_half has appropriate length and represents sy_int / 2
    // If the length of sy_half is still not `required_length`, we should adjust.
    while |sy_half| < required_length {
        sy_half := "0" + sy_half;
    }
    
    assert Str2Int(sy_half) == sy_int / 2;
    assert |sy_half| >= required_length; // Added for verification (although, it should be equal to required_length ideally)

    var r1_s := ModExpPow2_Helper(sx, sy_half, n - 1, sz);
    var r1_int := Str2Int(r1_s);
    var r_int := (r1_int * r1_int) % z_int;
    res := intToStr(r_int);
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
  var x_int := Str2Int(sx);
  var y_int := Str2Int(sy);
  var z_int := Str2Int(sz);

  var result: nat := 1;
  var base: nat := x_int % z_int;
  var exponent: nat := y_int;

  while exponent > 0
    invariant ValidBitString(intToStr(result))
    invariant ValidBitString(intToStr(base))
    invariant (result * Exp_int(base, exponent)) % z_int == Exp_int(x_int, y_int) % z_int
    invariant base < z_int
    invariant result < z_int || z_int == 1
    decreases exponent
  {
    if exponent % 2 == 1 {
      result := (result * base) % z_int;
    }
    base := (base * base) % z_int;
    exponent := exponent / 2;
  }
  res := intToStr(result);
}
// </vc-code>

