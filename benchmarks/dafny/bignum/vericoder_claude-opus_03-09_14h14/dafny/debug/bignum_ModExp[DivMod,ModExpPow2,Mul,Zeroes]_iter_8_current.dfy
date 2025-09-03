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

lemma DivBy2DecreasesLength(sy: string)
  requires ValidBitString(sy) && !AllZero(sy)
  requires |sy| > 1
  ensures forall quot :: ValidBitString(quot) && Str2Int(quot) == Str2Int(sy) / 2 ==> |quot| < |sy|
{
  // When dividing a non-zero number by 2, if the number has more than 1 bit,
  // the quotient will have fewer bits (since the MSB might become 0 and be dropped)
}

lemma DivBy2Properties(sy: string, quot: string, rem: string)
  requires ValidBitString(sy) && ValidBitString(quot) && ValidBitString(rem)
  requires !AllZero(sy)
  requires Str2Int(quot) == Str2Int(sy) / 2
  requires Str2Int(rem) == Str2Int(sy) % 2
  ensures AllZero(rem) <==> Str2Int(sy) % 2 == 0
  ensures !AllZero(rem) <==> Str2Int(sy) % 2 == 1
{
  // rem is either "0" or "1" when dividing by 2
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
  } else if |sy| == 1 {
    // Base case: sy is "1", so x^1 = x
    assert sy == "1";
    var _, modResult := DivMod(sx, sz);
    res := modResult;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
  } else {
    // |sy| > 1, so we can divide by 2
    DivBy2DecreasesLength(sy);
    var quot, rem := DivMod(sy, "10"); // Divide y by 2
    assert |quot| < |sy|;
    
    DivBy2Properties(sy, quot, rem);
    
    if AllZero(rem) {
      // y is even: x^y mod z = ((x^2 mod z)^(y/2)) mod z
      var xSquared := Mul(sx, sx);
      var _, xSquaredMod := DivMod(xSquared, sz);
      var halfPower := ModExp(xSquaredMod, quot, sz);
      res := halfPower;
      
      ExpIntProperties(Str2Int(sx), Str2Int(sy));
      
    } else {
      // y is odd: x^y mod z = (x * x^(y-1)) mod z
      assert Str2Int(sy) % 2 == 1;
      assert Str2Int(quot) == (Str2Int(sy) - 1) / 2;
      
      // Compute x^((y-1)/2) mod z recursively
      var halfPower := ModExp(sx, quot, sz);
      
      // Square it to get x^(y-1) mod z
      var squared := Mul(halfPower, halfPower);
      var _, squaredMod := DivMod(squared, sz);
      
      // Multiply by x to get x^y mod z
      var product := Mul(sx, squaredMod);
      var _, modResult := DivMod(product, sz);
      res := modResult;
      
      ExpIntProperties(Str2Int(sx), Str2Int(sy));
    }
  }
}
// </vc-code>

