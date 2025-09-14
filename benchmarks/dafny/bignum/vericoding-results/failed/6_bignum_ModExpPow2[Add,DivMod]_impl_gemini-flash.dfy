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

// <vc-helpers>
function Multiply(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(Multiply(s1, s2))
  ensures Str2Int(Multiply(s1, s2)) == Str2Int(s1) * Str2Int(s2)
{
  if Str2Int(s1) == 0 || Str2Int(s2) == 0 then "0"
  else if Str2Int(s1) == 1 then s2
  else if Str2Int(s2) == 1 then s1
  else
    var s1_int := Str2Int(s1);
    var s2_int := Str2Int(s2);
    // Directly convert the product to a bit string
    var k_product := s1_int * s2_int;
    NatToStr(k_product) // Use NatToStr for conversion
}

function Modulo(s_val: string, s_mod: string): string
  requires ValidBitString(s_val) && ValidBitString(s_mod)
  requires Str2Int(s_mod) > 0
  ensures ValidBitString(Modulo(s_val, s_mod))
  ensures Str2Int(Modulo(s_val, s_mod)) == Str2Int(s_val) % Str2Int(s_mod)
{
  var v := Str2Int(s_val);
  var m := Str2Int(s_mod);
  var r := v % m;
  NatToStr(r) // Use NatToStr for conversion
}

function NatToStr(val: nat): string
  ensures ValidBitString(NatToStr(val))
  ensures Str2Int(NatToStr(val)) == val
{
  if val == 0 then "0"
  else
    var res_str := "";
    var temp_val := val;
    while temp_val > 0
      invariant temp_val >= 0
      invariant ValidBitString(res_str)
      invariant temp_val == 0 ==> Str2Int(res_str) == val
      invariant temp_val > 0 ==> Str2Int(res_str) + (temp_val * Exp_int(2, |res_str|)) == val
      decreases temp_val
    {
      if temp_val % 2 == 1 then res_str := "1" + res_str
      else res_str := "0" + res_str;
      temp_val := temp_val / 2;
    }
    res_str
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
  var x := Str2Int(sx);
  var y := Str2Int(sy);
  var z := Str2Int(sz);

  if n == 0 {
    // This implies sy is "1" (2^0) or "0"
    if y == 1 {
      var res_val := Exp_int(x, 1) % z;
      res := NatToStr(res_val);
    } else { // y == 0
      var res_val := Exp_int(x, 0) % z;
      assert res_val == 1 % z;
      if z == 1 then res := "0"
      else
        res := "1";
    }
  } else {
    // sy = 2^n
    var sy_half_str: string;
    // sy is guaranteed to be 2^n or 0, and |sy| == n+1.
    // If sy is 2^n, it's a '1' followed by n '0's. sy[0..n] removes the last '0'.
    // If sy is 0, it's "0...0" for n+1 length. sy[0..n] is still "0...0" with length n.
    sy_half_str := sy[..n];

    // Added the following two assertions for verification purposes
    assert ValidBitString(sy_half_str);
    assert (Str2Int(sy) == Exp_int(2, n)) ==> (Str2Int(sy_half_str) == Exp_int(2, (n as nat) - 1));
    assert (Str2Int(sy) == 0) ==> (Str2Int(sy_half_str) == 0);
    assert |sy_half_str| == n;

    var power_x := ModExpPow2(sx, sy_half_str, (n as nat) - 1, sz);
    // power_x is x^(2^(n-1)) % z

    var power_x_int := Str2Int(power_x);
    var final_val := (power_x_int * power_x_int) % z;

    res := NatToStr(final_val);
  }
}
// </vc-code>

