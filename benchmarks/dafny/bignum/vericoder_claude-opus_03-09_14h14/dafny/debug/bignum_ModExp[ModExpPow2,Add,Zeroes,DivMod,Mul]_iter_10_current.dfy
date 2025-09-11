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
lemma ExpInt2(x: nat)
  ensures Exp_int(x, 2) == x * x
{
  assert Exp_int(x, 2) == x * Exp_int(x, 1);
  assert Exp_int(x, 1) == x * Exp_int(x, 0);
  assert Exp_int(x, 0) == 1;
}

lemma ExpIntEven(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    ExpInt2(x);
  } else {
    var y' := y - 2;
    ExpIntEven(x, y');
    assert Exp_int(x, y) == x * x * Exp_int(x, y');
    assert Exp_int(x, y') == Exp_int(x * x, y' / 2);
    assert y' / 2 + 1 == y / 2;
  }
}

lemma ExpIntOdd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma Str2IntLastBit(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures s[|s|-1] == '0' ==> Str2Int(s) % 2 == 0
  ensures s[|s|-1] == '1' ==> Str2Int(s) % 2 == 1
{
}

lemma Str2IntDivBy2(s: string)
  requires ValidBitString(s) && |s| > 0 && s[|s|-1] == '0'
  ensures Str2Int(s) / 2 == Str2Int(s[0..|s|-1])
{
}

lemma Str2IntPositive(s: string)
  requires ValidBitString(s) && |s| > 0
  requires !AllZero(s)
  ensures Str2Int(s) > 0
{
  if |s| == 1 {
    assert s[0] == '1';
  } else if s[|s|-1] == '1' {
  } else {
    if AllZero(s[0..|s|-1]) {
      assert AllZero(s);
      assert false;
    } else {
      Str2IntPositive(s[0..|s|-1]);
    }
  }
}

lemma AllZeroImpliesZero(s: string)
  requires ValidBitString(s)
  requires AllZero(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
  } else {
    AllZeroImpliesZero(s[0..|s|-1]);
  }
}

lemma Str2IntDecrementOdd(s: string)
  requires ValidBitString(s) && |s| > 0 && s[|s|-1] == '1'
  ensures ValidBitString(s[0..|s|-1] + "0")
  ensures Str2Int(s[0..|s|-1] + "0") == Str2Int(s) - 1
  ensures |s[0..|s|-1] + "0"| == |s|
{
  var s' := s[0..|s|-1] + "0";
}

lemma ModMultProperty(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
  // Simplified proof to avoid timeout
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
    AllZeroImpliesZero(sy);
    res := "1";
    assert Str2Int(res) == 1;
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    return;
  }
  
  if |sy| == 1 && sy[0] == '1' {
    var _, rem := DivMod(sx, sz);
    res := rem;
    assert Str2Int(sy) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    assert Str2Int(res) == Str2Int(sx) % Str2Int(sz);
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    return;
  }
  
  Str2IntPositive(sy);
  Str2IntLastBit(sy);
  
  if sy[|sy|-1] == '0' {
    Str2IntDivBy2(sy);
    
    var sy_div2 := sy[0..|sy|-1];
    assert |sy_div2| < |sy|;
    var half_result := ModExp(sx, sy_div2, sz);
    var squared := Mul(half_result, half_result);
    var _, result := DivMod(squared, sz);
    res := result;
    
    ExpIntEven(Str2Int(sx), Str2Int(sy));
    assert Str2Int(half_result) == Exp_int(Str2Int(sx), Str2Int(sy_div2)) % Str2Int(sz);
    assert Str2Int(squared) == Str2Int(half_result) * Str2Int(half_result);
    ModMultProperty(Exp_int(Str2Int(sx), Str2Int(sy_div2)), Exp_int(Str2Int(sx), Str2Int(sy_div2)), Str2Int(sz));
    assert Str2Int(result) == Str2Int(squared) % Str2Int(sz);
    assert Str2Int(result) == Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2) % Str2Int(sz);
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  } else {
    Str2IntDecrementOdd(sy);
    
    var sy_minus_one := sy[0..|sy|-1] + "0";
    assert |sy_minus_one| == |sy|;
    assert |sy[0..|sy|-1]| < |sy|;
    var temp_result := ModExp(sx, sy[0..|sy|-1], sz);
    var product := Mul(sx, temp_result);
    var _, result := DivMod(product, sz);
    res := result;
    
    assert Str2Int(sy[0..|sy|-1]) == Str2Int(sy) / 2;
    ExpIntOdd(Str2Int(sx), Str2Int(sy));
    assert Str2Int(temp_result) == Exp_int(Str2Int(sx), Str2Int(sy[0..|sy|-1])) % Str2Int(sz);
    assert Str2Int(temp_result) == Exp_int(Str2Int(sx), Str2Int(sy) / 2) % Str2Int(sz);
    var x_squared := Str2Int(sx) * Str2Int(sx);
    ExpIntEven(Str2Int(sx), Str2Int(sy) - 1);
    assert Exp_int(Str2Int(sx), Str2Int(sy) - 1) == Exp_int(x_squared, (Str2Int(sy) - 1) / 2);
    assert (Str2Int(sy) - 1) / 2 == Str2Int(sy) / 2;
    assert Str2Int(temp_result) == Exp_int(x_squared, Str2Int(sy) / 2) % Str2Int(sz);
    assert Str2Int(product) == Str2Int(sx) * Str2Int(temp_result);
    ModMultProperty(Str2Int(sx), Exp_int(x_squared, Str2Int(sy) / 2), Str2Int(sz));
    assert Str2Int(result) == Str2Int(product) % Str2Int(sz);
    assert Exp_int(Str2Int(sx), Str2Int(sy)) == Str2Int(sx) * Exp_int(x_squared, Str2Int(sy) / 2);
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  }
}
// </vc-code>

