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
    calc {
      Exp_int(x, y);
    == 
      x * Exp_int(x, 2 * y - 1);
    == 
      x * x * Exp_int(x, 2 * (y - 1));
    == { Exp_int_double(x, y - 1); }
      x * x * Exp_int(x, y - 1) * Exp_int(x, y - 1);
    ==
      Exp_int(x * x, half);
    }
  }
}

lemma Exp_int_double(x: nat, y: nat)
  ensures Exp_int(x, 2 * y) == Exp_int(x, y) * Exp_int(x, y)
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
  } else {
    calc {
      Exp_int(x, 2 * y);
    ==
      x * Exp_int(x, 2 * y - 1);
    ==
      x * x * Exp_int(x, 2 * y - 2);
    == { assert 2 * y - 2 == 2 * (y - 1); Exp_int_double(x, y - 1); }
      x * x * Exp_int(x, y - 1) * Exp_int(x, y - 1);
    ==
      (x * Exp_int(x, y - 1)) * (x * Exp_int(x, y - 1));
    ==
      Exp_int(x, y) * Exp_int(x, y);
    }
  }
}

lemma Exp_int_odd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma Str2IntZero(s: string)
  requires ValidBitString(s)
  requires AllZero(s)
  ensures Str2Int(s) == 0
{
  if |s| > 0 {
    assert s[|s|-1] == '0';
    Str2IntZero(s[0..|s|-1]);
  }
}

lemma Str2IntLastBit(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) % 2 == if s[|s|-1] == '1' then 1 else 0
{
}

lemma Str2IntDivBy2(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s[0..|s|-1]) == Str2Int(s) / 2
{
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var carry := 0;
  var result := "";
  var i1 := |s1| - 1;
  var i2 := |s2| - 1;
  
  while i1 >= 0 || i2 >= 0 || carry > 0
    invariant ValidBitString(result)
    invariant -1 <= i1 < |s1|
    invariant -1 <= i2 < |s2|
    invariant 0 <= carry <= 1
  {
    var bit1 := if i1 >= 0 then (if s1[i1] == '1' then 1 else 0) else 0;
    var bit2 := if i2 >= 0 then (if s2[i2] == '1' then 1 else 0) else 0;
    
    var sum := bit1 + bit2 + carry;
    result := (if sum % 2 == 1 then "1" else "0") + result;
    carry := sum / 2;
    
    if i1 >= 0 { i1 := i1 - 1; }
    if i2 >= 0 { i2 := i2 - 1; }
  }
  
  res := result;
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
  Str2IntZero(s);
}

method IsZero(s: string) returns (b: bool)
  requires ValidBitString(s)
  ensures b == (Str2Int(s) == 0)
{
  b := true;
  for i := 0 to |s|
    invariant b == (forall j | 0 <= j < i :: s[j] == '0')
  {
    if s[i] != '0' {
      b := false;
      break;
    }
  }
  if b && |s| > 0 {
    assert AllZero(s);
    Str2IntZero(s);
  }
}

method IsOdd(s: string) returns (b: bool)
  requires ValidBitString(s)
  requires |s| > 0
  ensures b == (Str2Int(s) % 2 == 1)
{
  b := s[|s| - 1] == '1';
  Str2IntLastBit(s);
}

method DivBy2(s: string) returns (res: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) / 2
{
  if |s| == 1 {
    res := "0";
  } else {
    res := s[0..|s| - 1];
    Str2IntDivBy2(s);
  }
}

method SubOne(s: string) returns (res: string)
  requires ValidBitString(s)
  requires Str2Int(s) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) - 1
{
  var carry := true;
  var result := "";
  for i := |s| - 1 downto 0
    invariant ValidBitString(result)
  {
    if carry {
      if s[i] == '1' {
        result := "0" + result;
        carry := false;
      } else {
        result := "1" + result;
      }
    } else {
      result := [s[i]] + result;
    }
  }
  res := result;
}

method Mult(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  res := "0";
  var temp := s1;
  for i := |s2| - 1 downto 0
    invariant ValidBitString(res)
    invariant ValidBitString(temp)
  {
    if s2[i] == '1' {
      res := Add(res, temp);
    }
    temp := Add(temp, temp);
  }
}

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  var carry := false;
  var result := "";
  var i1 := |s1| - 1;
  var i2 := |s2| - 1;
  
  while i1 >= 0 || i2 >= 0
    invariant ValidBitString(result)
    invariant -1 <= i1 < |s1|
    invariant -1 <= i2 < |s2|
  {
    var bit1 := if i1 >= 0 then (if s1[i1] == '1' then 1 else 0) else 0;
    var bit2 := if i2 >= 0 then (if s2[i2] == '1' then 1 else 0) else 0;
    var borrow := if carry then 1 else 0;
    
    var diff := bit1 - bit2 - borrow;
    if diff < 0 {
      diff := diff + 2;
      carry := true;
    } else {
      carry := false;
    }
    
    result := (if diff == 1 then "1" else "0") + result;
    
    if i1 >= 0 { i1 := i1 - 1; }
    if i2 >= 0 { i2 := i2 - 1; }
  }
  
  res := result;
}

method Mod(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)
{
  res := s1;
  while Str2Int(res) >= Str2Int(s2)
    invariant ValidBitString(res)
    invariant Str2Int(res) % Str2Int(s2) == Str2Int(s1) % Str2Int(s2)
    decreases Str2Int(res)
  {
    res := Sub(res, s2);
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
  var zero := IsZero(sy);
  if zero {
    res := "1";
    assert Str2Int(sy) == 0;
    Exp_int_zero(Str2Int(sx));
  } else {
    var odd := IsOdd(sy);
    if odd {
      assert Str2Int(sy) % 2 == 1;
      Exp_int_odd(Str2Int(sx), Str2Int(sy));
      var y_minus_1 := SubOne(sy);
      var temp := ModExp(sx, y_minus_1, sz);
      var product := Mult(sx, temp);
      res := Mod(product, sz);
    } else {
      assert Str2Int(sy) % 2 == 0;
      assert Str2Int(sy) > 0;
      Exp_int_even(Str2Int(sx), Str2Int(sy));
      var y_div_2 := DivBy2(sy);
      var x_squared := Mult(sx, sx);
      var x_squared_mod := Mod(x_squared, sz);
      res := ModExp(x_squared_mod, y_div_2, sz);
    }
  }
}
// </vc-code>

