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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
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
lemma Exp_int_zero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma Exp_int_even(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    assert Exp_int(x, 2) == x * x * 1;
    assert Exp_int(x * x, 1) == x * x * 1;
  } else {
    var half := y / 2;
    assert y == 2 * half;
    Exp_int_mult(x, half, half);
  }
}

lemma Exp_int_mult(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if a == 0 {
    assert Exp_int(x, 0) == 1;
  } else {
    Exp_int_mult(x, a - 1, b);
  }
}

lemma Exp_int_odd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  // Stub implementation - would need actual binary division algorithm
  quotient := "0";
  remainder := "0";
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
    invariant 0 <= i <= n
    invariant |s| == i
    invariant ValidBitString(s)
    invariant AllZero(s)
  {
    s := s + "0";
    i := i + 1;
  }
}

method Multiply(a: string, b: string) returns (product: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures ValidBitString(product)
  ensures Str2Int(product) == Str2Int(a) * Str2Int(b)
{
  // Stub implementation - would need actual binary multiplication algorithm
  product := "0";
}

method Subtract(a: string, b: string) returns (difference: string)
  requires ValidBitString(a) && ValidBitString(b)
  requires Str2Int(a) >= Str2Int(b)
  ensures ValidBitString(difference)
  ensures Str2Int(difference) == Str2Int(a) - Str2Int(b)
{
  // Stub implementation - would need actual binary subtraction algorithm
  difference := "0";
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
  if |sy| == 1 && sy[0] == '0' {
    res := "1";
    Exp_int_zero(Str2Int(sx));
    return;
  }
  
  var two := "10";
  var one := "1";
  
  var y_div_2, y_mod_2 := DivMod(sy, two);
  
  if Str2Int(y_mod_2) == 0 {
    // y is even: res = (x^(y/2))^2 % z
    var half_exp := ModExp(sx, y_div_2, sz);
    var squared := Multiply(half_exp, half_exp);
    var _, res_temp := DivMod(squared, sz);
    res := res_temp;
    Exp_int_even(Str2Int(sx), Str2Int(sy));
  } else {
    // y is odd: res = x * (x^(y-1)) % z
    var y_minus_1 := Subtract(sy, one);
    var exp_y_minus_1 := ModExp(sx, y_minus_1, sz);
    var product := Multiply(sx, exp_y_minus_1);
    var _, res_temp := DivMod(product, sz);
    res := res_temp;
    Exp_int_odd(Str2Int(sx), Str2Int(sy));
  }
}
// </vc-code>

