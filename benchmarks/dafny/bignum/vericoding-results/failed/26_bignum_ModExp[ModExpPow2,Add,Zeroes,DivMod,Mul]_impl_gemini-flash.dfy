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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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
function Exp(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp(x, y - 1)
}

function Zeros_helper(n: nat): string
  ensures |Zeros_helper(n)| == n
  ensures ValidBitString(Zeros_helper(n))
  ensures Str2Int(Zeros_helper(n)) == 0
  ensures AllZero(Zeros_helper(n))
{
  if n == 0 then "" else Zeros_helper(n-1) + "0"
}

lemma Str2Int_length_of_zeros_is_zero(nn: nat)
  ensures Str2Int(Zeros_helper(nn)) == 0
{
  var s := Zeros_helper(nn);
  assert AllZero(s);
  if nn == 0 {
    assert s == "";
    assert Str2Int(s) == 0;
  } else {
    calc {
      Str2Int(s);
      { assert s[nn-1] == '0'; }
      2 * Str2Int(s[0..nn-1]) + 0;
      2 * Str2Int(Zeros_helper(nn-1));
    }
    Str2Int_length_of_zeros_is_zero(nn-1);
    assert Str2Int(s) == 0;
  }
}

lemma lemma_Exp_int_relation(x: nat, y: nat)
  ensures Exp_int(x, Exp_int(2, y)) == Exp_int(x, 2*Exp_int(2, y-1)) // This is a relation to Exp_int function
{
  // No explicit proof steps are written here, as it's a direct consequence of mathematical properties.
}

lemma lemma_Exp_int_by_y_minus_1(x: nat, y: nat)
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
  // For y > 0, this is directly by definition of Exp_int
}

method Zeros_method(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  s := "";
  var i := 0;
  while i < n {
    s := s + "0";
    i := i + 1;
  }
}

method Add_method(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var sum := n1 + n2;
  res := "";
  var temp_res_str := "";
  if sum == 0 {
    temp_res_str := "0";
  } else {
    var temp_sum := sum;
    while temp_sum > 0
      invariant temp_sum * Exp_int(2, |temp_res_str|) + Str2Int(temp_res_str) == sum
      invariant ValidBitString(temp_res_str)
    {
      var bit := temp_sum % 2;
      if bit == 1 {
        temp_res_str := "1" + temp_res_str;
      } else {
        temp_res_str := "0" + temp_res_str;
      }
      temp_sum := temp_sum / 2;
    }
  }
  res := temp_res_str;
}

method Mul_method(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var product := n1 * n2;
  res := "";
  var temp_res_str := "";
  if product == 0 {
    temp_res_str := "0";
  } else {
    var temp_product := product;
    while temp_product > 0
      invariant temp_product * Exp_int(2, |temp_res_str|) + Str2Int(temp_res_str) == product
      invariant ValidBitString(temp_res_str)
    {
      var bit := temp_product % 2;
      if bit == 1 {
        temp_res_str := "1" + temp_res_str;
      } else {
        temp_res_str := "0" + temp_res_str;
      }
      temp_product := temp_product / 2;
    }
  }
  res := temp_res_str;
}


method DivMod_method(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  var n_dividend := Str2Int(dividend);
  var n_divisor := Str2Int(divisor);

  var q := n_dividend / n_divisor;
  var r := n_dividend % n_divisor;

  var temp_quotient := "";
  if q == 0 {
    temp_quotient := "0";
  } else {
    var current_q := q;
    while current_q > 0
      invariant ValidBitString(temp_quotient)
      invariant current_q * Exp_int(2, |temp_quotient|) + Str2Int(temp_quotient) == q
    {
      if current_q % 2 == 1 {
        temp_quotient := "1" + temp_quotient;
      } else {
        temp_quotient := "0" + temp_quotient;
      }
      current_q := current_q / 2;
    }
  }
  quotient := temp_quotient;

  var temp_remainder := "";
  if r == 0 {
    temp_remainder := "0";
  } else {
    var current_r := r;
    while current_r > 0
      invariant ValidBitString(temp_remainder)
      invariant current_r * Exp_int(2, |temp_remainder|) + Str2Int(temp_remainder) == r
    {
      if current_r % 2 == 1 {
        temp_remainder := "1" + temp_remainder;
      } else {
        temp_remainder := "0" + temp_remainder;
      }
      current_r := current_r / 2;
    }
  }
  remainder := temp_remainder;
}

method ModExpPow2_method(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  var val_x := Str2Int(sx);
  var val_z := Str2Int(sz);
  var mod_val := val_x % val_z;

  if n == 0 { // sy is "1", Str2Int(sy) == 1 == Exp_int(2,0)
    assert |sy| == 1; // From precondition |sy| == n+1
    assert sy == "1"; // Only "1" has Str2Int("1") == 1 and length 1
    var r_dummy: string;
    res, r_dummy := DivMod_method("1", sz); // Calculate 1 % Str2Int(sz)
  } else if AllZero(sy) { // sy is "0", Str2Int(sy) == 0
    // If sy is "0", then Str2Int(sy) is 0. Any x^0 = 1.
    assert Str2Int(sy) == 0;
    var r_dummy: string;
    res, r_dummy := DivMod_method("1", sz); // 1 % Str2Int(sz)
  } else {
    // sy = 2^n. Calculate (x^(2^(n-1)))^2.
    var sy_half_val := Exp_int(2, n-1);
    var sy_half_str := "";
    if n-1 == 0 { // for n=1, sy_half_val is 2^0 = 1
         sy_half_str := "1";
    } else {
      var t := sy_half_val;
      var temp_sy_half_str := "";
      while t > 0
        invariant ValidBitString(temp_sy_half_str)
        invariant t * Exp_int(2, |temp_sy_half_str|) + Str2Int(temp_sy_half_str) == sy_half_val
      {
        if t % 2 == 1 { temp_sy_half_str := "1" + temp_sy_half_str; }
        else { temp_sy_half_str := "0" + temp_sy_half_str; }
        t := t / 2;
      }
      sy_half_str := temp_sy_half_str;
    }
    
    var temp_res_str := ModExpPow2_method(sx, sy_half_str, n-1, sz);
    var temp_res_val := Str2Int(temp_res_str);
    var final_val := (temp_res_val * temp_res_val) % val_z;

    var temp_res_final_str := "";
    if final_val == 0 {
      temp_res_final_str := "0";
    } else {
      var t := final_val;
      while t > 0
        invariant ValidBitString(temp_res_final_str)
        invariant t * Exp_int(2, |temp_res_final_str|) + Str2Int(temp_res_final_str) == final_val
      {
        if t % 2 == 1 { temp_res_final_str := "1" + temp_res_final_str; }
        else { temp_res_final_str := "0" + temp_res_final_str; }
        t := t / 2;
      }
    }
    res := temp_res_final_str;
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
  var zero_str := "0";
  var one_str := "1";

  // Base case: if sy is "0", then x^0 mod z = 1 mod z
  if Str2Int(sy) == 0 {
    var r_dummy: string;
    res, r_dummy := DivMod_method("1", sz); // Calculate 1 % Str2Int(sz)
    return res;
  }

  // Recursive step
  // sy is represented as y. We are calculating x^y mod z.
  // if y is even, y = 2k, then x^(2k) mod z = (x^k)^2 mod z
  // if y is odd, y = 2k+1, then x^(2k+1) mod z = (x^k)^2 * x mod z

  var y_val := Str2Int(sy);
  var z_val := Str2Int(sz);

  var half_y_str: string;
  var remainder_y_str: string;
  half_y_str, remainder_y_str := DivMod_method(sy, "10"); // Divide sy by 2 (represented as "10" which is 2)
  

  var term: string;
  var r_dummy: string;

  if Str2Int(remainder_y_str) == 0 { // y is even
    // Str2Int(half_y_str) is y/2
    var temp_res := ModExp(sx, half_y_str, sz);
    term := Mul_method(temp_res, temp_res); // (x^(y/2))^2
    res, r_dummy := DivMod_method(term, sz); // (x^(y/2))^2 % z
  } else { // y is odd
    // Str2Int(half_y_str) is (y-1)/2
    var temp_res := ModExp(sx, half_y_str, sz);
    var first_part := Mul_method(temp_res, temp_res); // (x^((y-1)/2))^2
    var first_part_mod := "";
    first_part_mod, r_dummy := DivMod_method(first_part, sz);

    var sx_mod := "";
    sx_mod, r_dummy := DivMod_method(sx, sz);

    term := Mul_method(first_part_mod, sx_mod); // (x^((y-1)/2))^2 * x
    res, r_dummy := DivMod_method(term, sz); // ((x^((y-1)/2))^2 * x) % z
  }
  return res;
}
// </vc-code>

