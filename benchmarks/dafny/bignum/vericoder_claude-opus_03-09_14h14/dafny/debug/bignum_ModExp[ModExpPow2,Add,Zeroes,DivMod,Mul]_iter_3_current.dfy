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
  assert Exp_int(x, 1) == x * 1;
  assert Exp_int(x, 1) == x;
  assert Exp_int(x, 2) == x * x;
}

lemma ExpIntEven(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    ExpInt2(x);
    assert Exp_int(x, 2) == x * x;
    assert Exp_int(x * x, 1) == x * x * Exp_int(x * x, 0);
    assert Exp_int(x * x, 0) == 1;
    assert Exp_int(x * x, 1) == x * x;
  } else {
    assert y >= 2;
    var y' := y - 2;
    assert y' % 2 == 0;
    assert y' / 2 == y / 2 - 1;
    ExpIntEven(x, y');
    assert Exp_int(x, y) == x * x * Exp_int(x, y');
    assert Exp_int(x, y') == Exp_int(x * x, y' / 2);
    assert Exp_int(x, y) == x * x * Exp_int(x * x, y' / 2);
    assert Exp_int(x, y) == Exp_int(x * x, y' / 2 + 1);
    assert y' / 2 + 1 == y / 2;
  }
}

lemma ExpIntOdd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
  // This follows directly from the definition of Exp_int
}

lemma Str2IntLastBit(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures s[|s|-1] == '0' ==> Str2Int(s) % 2 == 0
  ensures s[|s|-1] == '1' ==> Str2Int(s) % 2 == 1
{
  // By definition of Str2Int
}

lemma Str2IntDivBy2(s: string)
  requires ValidBitString(s) && |s| > 0 && s[|s|-1] == '0'
  ensures Str2Int(s) / 2 == Str2Int(s[0..|s|-1])
{
  // By definition of Str2Int when last bit is 0
}

lemma Str2IntSubOne(s: string, s_minus_one: string)
  requires ValidBitString(s) && |s| > 0 && s[|s|-1] == '1'
  requires ValidBitString(s_minus_one)
  requires Str2Int(s_minus_one) == Str2Int(s) - 1
  ensures Str2Int(s_minus_one) / 2 == (Str2Int(s) - 1) / 2
{
  // Direct from the requirement
}

lemma Str2IntOddMinusOne(s: string)
  requires ValidBitString(s) && |s| > 0 && s[|s|-1] == '1'
  ensures |s| > 1 ==> Str2Int(s[0..|s|-1] + "0") == Str2Int(s) - 1
  ensures |s| == 1 ==> Str2Int("0") == Str2Int(s) - 1
{
  // When last bit is 1, replacing it with 0 subtracts 1
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
    // y = 0, so x^0 = 1
    res := "1";
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert Str2Int(res) == 1;
    assert 1 % Str2Int(sz) == 1;
    return;
  }
  
  if |sy| == 1 && sy[0] == '1' {
    // y = 1, so x^1 = x
    var _, rem := DivMod(sx, sz);
    res := rem;
    assert Str2Int(sy) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    return;
  }
  
  // Check if sy is even (last bit is 0) or odd (last bit is 1)
  if sy[|sy|-1] == '0' {
    // sy is even
    Str2IntLastBit(sy);
    var sy_div2 := sy[0..|sy|-1];
    assert ValidBitString(sy_div2);
    assert |sy_div2| < |sy|;
    Str2IntDivBy2(sy);
    assert Str2Int(sy_div2) == Str2Int(sy) / 2;
    
    // Compute sx^(sy/2) % sz recursively
    var temp := ModExp(sx, sy_div2, sz);
    
    // Compute (temp * temp) % sz
    var temp_squared := Mul(temp, temp);
    var _, rem := DivMod(temp_squared, sz);
    res := rem;
    
    ExpIntEven(Str2Int(sx), Str2Int(sy));
  } else {
    // sy is odd
    assert |sy| >= 2; // Because we handled |sy| == 1 cases above
    Str2IntLastBit(sy);
    
    // Compute sy - 1 by changing last bit from '1' to '0'
    var sy_minus_one := sy[0..|sy|-1] + "0";
    
    assert ValidBitString(sy_minus_one);
    assert |sy_minus_one| == |sy|;
    Str2IntOddMinusOne(sy);
    assert Str2Int(sy_minus_one) == Str2Int(sy) - 1;
    
    // Since sy_minus_one ends with '0', we can reduce its length
    var sy_minus_one_reduced := sy_minus_one[0..|sy_minus_one|-1];
    assert ValidBitString(sy_minus_one_reduced);
    assert |sy_minus_one_reduced| < |sy|;
    Str2IntDivBy2(sy_minus_one);
    assert Str2Int(sy_minus_one_reduced) == Str2Int(sy_minus_one) / 2;
    
    // First compute sx^((sy-1)/2) % sz
    var temp_half := ModExp(sx, sy_minus_one_reduced, sz);
    
    // Square it to get sx^(sy-1) % sz
    var temp_squared := Mul(temp_half, temp_half);
    var _, temp := DivMod(temp_squared, sz);
    
    // Compute (sx * temp) % sz
    var sx_times_temp := Mul(sx, temp);
    var quot, rem := DivMod(sx_times_temp, sz);
    res := rem;
    
    ExpIntOdd(Str2Int(sx), Str2Int(sy));
    ExpIntEven(Str2Int(sx), Str2Int(sy) - 1);
  }
}
// </vc-code>

