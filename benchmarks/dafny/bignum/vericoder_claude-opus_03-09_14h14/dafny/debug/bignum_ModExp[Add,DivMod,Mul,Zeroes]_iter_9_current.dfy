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
lemma ExpRecursive(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma ExpBase(x: nat)
  ensures Exp_int(x, 2) == x * x
{
  calc {
    Exp_int(x, 2);
    == x * Exp_int(x, 1);
    == x * (x * Exp_int(x, 0));
    == x * x * 1;
    == x * x;
  }
}

lemma ExpEven(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    ExpBase(x);
    assert Exp_int(x, 2) == x * x;
    assert Exp_int(x * x, 1) == x * x * Exp_int(x * x, 0);
    assert Exp_int(x * x, 1) == x * x * 1;
    assert Exp_int(x * x, 1) == x * x;
  } else {
    assert y / 2 > 1;
    ExpEven(x, y - 2);
    assert Exp_int(x, y - 2) == Exp_int(x * x, (y - 2) / 2);
    assert (y - 2) / 2 == y / 2 - 1;
    assert Exp_int(x, y) == x * x * Exp_int(x, y - 2);
    assert Exp_int(x, y) == x * x * Exp_int(x * x, y / 2 - 1);
    assert Exp_int(x, y) == Exp_int(x * x, y / 2);
  }
}

lemma ExpOdd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
{
  if y == 1 {
    assert Exp_int(x, 1) == x;
    assert Exp_int(x * x, 0) == 1;
    assert x * Exp_int(x * x, 0) == x;
  } else {
    assert y / 2 >= 1;
    ExpEven(x, y - 1);
    assert Exp_int(x, y - 1) == Exp_int(x * x, (y - 1) / 2);
    assert (y - 1) / 2 == y / 2;
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    assert Exp_int(x, y) == x * Exp_int(x * x, y / 2);
  }
}

lemma Str2IntPositive(s: string)
  requires ValidBitString(s) && |s| > 0 && s[|s|-1] == '1'
  ensures Str2Int(s) >= 1
{
  if |s| == 1 {
    assert s == "1";
    assert Str2Int(s) == 1;
  } else {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
    assert Str2Int(s) >= 1;
  }
}

lemma AllZeroImpliesZeroValue(s: string)
  requires ValidBitString(s) && AllZero(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    assert s[|s|-1] == '0';
    if |s| == 1 {
      assert Str2Int(s) == 0;
    } else {
      AllZeroImpliesZeroValue(s[0..|s|-1]);
      assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 0;
      assert Str2Int(s) == 0;
    }
  }
}

lemma DivBy2ReducesLength(s: string, ydiv2: string)
  requires ValidBitString(s) && |s| > 0 && Str2Int(s) > 1
  requires ValidBitString(ydiv2) && Str2Int(ydiv2) == Str2Int(s) / 2
  ensures |ydiv2| <= |s|
  ensures Str2Int(ydiv2) < Str2Int(s)
{
  assert Str2Int(ydiv2) == Str2Int(s) / 2;
  assert Str2Int(s) > 1;
  assert Str2Int(ydiv2) < Str2Int(s);
}

lemma Str2IntIsOne(s: string)
  requires ValidBitString(s) && Str2Int(s) == 1
  ensures s == "1" || (|s| >= 2 && AllZero(s[0..|s|-1]) && s[|s|-1] == '1')
{
  if |s| == 1 {
    assert s[0] == '0' || s[0] == '1';
    if s[0] == '0' {
      assert Str2Int(s) == 0;
      assert false;
    } else {
      assert s == "1";
    }
  } else {
    assert |s| >= 2;
    if s[|s|-1] == '0' {
      assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]);
      assert Str2Int(s) % 2 == 0;
      assert Str2Int(s) != 1;
      assert false;
    } else {
      assert s[|s|-1] == '1';
      assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
      assert Str2Int(s[0..|s|-1]) == 0;
      AllZeroImpliesZeroValue(s[0..|s|-1]);
      assert AllZero(s[0..|s|-1]);
    }
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
  if sy == "0" {
    res := "1";
    return;
  }
  
  // Check if sy represents 1 (could be "1" or "01" or "001" etc.)
  if Str2Int(sy) == 1 {
    Str2IntIsOne(sy);
    var _, rem := DivMod(sx, sz);
    res := rem;
    return;
  }
  
  // At this point Str2Int(sy) > 1
  assert Str2Int(sy) > 1;
  
  var two := "10";
  var _, ymod2 := DivMod(sy, two);
  var ydiv2, _ := DivMod(sy, two);
  
  assert Str2Int(ydiv2) == Str2Int(sy) / 2;
  assert Str2Int(ydiv2) < Str2Int(sy);
  DivBy2ReducesLength(sy, ydiv2);
  assert |ydiv2| <= |sy|;
  
  if ymod2 == "0" {
    assert Str2Int(sy) % 2 == 0;
    var x_squared := Mul(sx, sx);
    var _, x_squared_mod := DivMod(x_squared, sz);
    ExpEven(Str2Int(sx), Str2Int(sy));
    if |ydiv2| < |sy| {
      res := ModExp(x_squared_mod, ydiv2, sz);
    } else {
      assert |ydiv2| == |sy|;
      assert Str2Int(ydiv2) < Str2Int(sy);
      res := ModExp(x_squared_mod, ydiv2, sz);
    }
  } else {
    assert Str2Int(sy) % 2 == 1;
    var x_squared := Mul(sx, sx);
    var _, x_squared_mod := DivMod(x_squared, sz);
    ExpOdd(Str2Int(sx), Str2Int(sy));
    if |ydiv2| < |sy| {
      var temp := ModExp(x_squared_mod, ydiv2, sz);
      var _, x_mod := DivMod(sx, sz);
      var product := Mul(x_mod, temp);
      var _, result := DivMod(product, sz);
      res := result;
    } else {
      assert |ydiv2| == |sy|;
      assert Str2Int(ydiv2) < Str2Int(sy);
      var temp := ModExp(x_squared_mod, ydiv2, sz);
      var _, x_mod := DivMod(sx, sz);
      var product := Mul(x_mod, temp);
      var _, result := DivMod(product, sz);
      res := result;
    }
  }
}
// </vc-code>

