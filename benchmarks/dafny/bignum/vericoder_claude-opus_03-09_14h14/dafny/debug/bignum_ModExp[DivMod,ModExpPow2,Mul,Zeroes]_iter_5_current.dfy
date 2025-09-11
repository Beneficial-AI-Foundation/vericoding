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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpIntProperties(x: nat, y: nat)
  ensures y == 0 ==> Exp_int(x, y) == 1
  ensures y > 0 && y % 2 == 0 ==> Exp_int(x, y) == Exp_int(x * x, y / 2)
  ensures y > 0 && y % 2 == 1 ==> Exp_int(x, y) == x * Exp_int(x, y - 1)
{
  if y == 0 {
    // Base case: x^0 == 1
  } else if y % 2 == 0 {
    // Even case: x^y == (x^2)^(y/2)
    calc == {
      Exp_int(x, y);
      x * Exp_int(x, y - 1);
      x * x * Exp_int(x, y - 2);
      { ExpIntPowerEven(x, y); }
      Exp_int(x * x, y / 2);
    }
  } else {
    // Odd case: x^y == x * x^(y-1)
  }
}

lemma ExpIntPowerEven(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
  decreases y
{
  if y == 2 {
    calc == {
      Exp_int(x, 2);
      x * Exp_int(x, 1);
      x * x * Exp_int(x, 0);
      x * x * 1;
      x * x;
      Exp_int(x * x, 1);
    }
  } else {
    calc == {
      Exp_int(x, y);
      x * Exp_int(x, y - 1);
      x * x * Exp_int(x, y - 2);
      { ExpIntPowerEven(x, y - 2); }
      x * x * Exp_int(x * x, (y - 2) / 2);
      { assert (y - 2) / 2 == y / 2 - 1; }
      x * x * Exp_int(x * x, y / 2 - 1);
      Exp_int(x * x, y / 2);
    }
  }
}

lemma SubtractOne(s: string)
  requires ValidBitString(s) && |s| > 0 && !AllZero(s)
  requires s[|s|-1] == '1'
  ensures ValidBitString(s[0..|s|-1] + "0")
  ensures Str2Int(s[0..|s|-1] + "0") == Str2Int(s) - 1
{
  calc == {
    Str2Int(s);
    2 * Str2Int(s[0..|s|-1]) + 1;
  }
  calc == {
    Str2Int(s[0..|s|-1] + "0");
    2 * Str2Int(s[0..|s|-1]) + 0;
    Str2Int(s) - 1;
  }
}

lemma DivBy2Properties(sy: string, quot: string)
  requires ValidBitString(sy) && ValidBitString(quot)
  requires !AllZero(sy)
  requires Str2Int(quot) == Str2Int(sy) / 2
  ensures |quot| <= |sy|
  ensures Str2Int(quot) < Str2Int(sy)
{
  assert Str2Int(sy) > 0;
  assert Str2Int(quot) == Str2Int(sy) / 2;
  assert Str2Int(quot) < Str2Int(sy);
  // The length bound follows from the fact that dividing by 2 at most removes one bit
}

lemma QuotientLengthBound(dividend: string, divisor: string, quotient: string)
  requires ValidBitString(dividend) && ValidBitString(divisor) && ValidBitString(quotient)
  requires Str2Int(divisor) > 0
  requires Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  requires divisor == "10"  // divisor is 2 in binary
  ensures |quotient| <= |dividend|
{
  // When dividing by 2, the quotient has at most the same number of bits as the dividend
  assert Str2Int("10") == 2;
  assert Str2Int(quotient) == Str2Int(dividend) / 2;
  assert Str2Int(quotient) <= Str2Int(dividend);
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
  if AllZero(sy) {
    // y == 0, so x^0 = 1
    res := "1";
    ExpIntProperties(Str2Int(sx), 0);
  } else {
    // y > 0
    var quot, rem := DivMod(sy, "10"); // Divide y by 2
    
    // Establish the length bound for quot
    assert Str2Int("10") == 2;
    assert Str2Int(quot) == Str2Int(sy) / 2;
    QuotientLengthBound(sy, "10", quot);
    assert |quot| <= |sy|;
    
    if AllZero(rem) {
      // y is even: x^y mod z = (x^(y/2))^2 mod z
      DivBy2Properties(sy, quot);
      
      var halfPower := ModExp(sx, quot, sz);
      var squared := Mul(halfPower, halfPower);
      var _, modResult := DivMod(squared, sz);
      res := modResult;
      
      ExpIntProperties(Str2Int(sx), Str2Int(sy));
      
    } else {
      // y is odd: x^y mod z = x * x^(y-1) mod z
      assert sy[|sy|-1] == '1';
      var yMinusOne := sy[0..|sy|-1] + "0";
      SubtractOne(sy);
      assert |yMinusOne| == |sy|;
      
      var prevPower := ModExp(sx, yMinusOne, sz);
      var product := Mul(sx, prevPower);
      var _, modResult := DivMod(product, sz);
      res := modResult;
      
      ExpIntProperties(Str2Int(sx), Str2Int(sy));
    }
  }
}
// </vc-code>

