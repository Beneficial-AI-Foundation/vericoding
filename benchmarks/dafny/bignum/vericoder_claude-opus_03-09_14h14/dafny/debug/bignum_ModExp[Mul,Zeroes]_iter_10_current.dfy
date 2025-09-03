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
lemma Exp_int_zero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma Exp_int_even(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    assert Exp_int(x, 2) == x * x;
    assert Exp_int(x * x, 1) == x * x;
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
    assert Exp_int(x, a) == 1;
    assert Exp_int(x, a + b) == Exp_int(x, b);
  } else {
    assert Exp_int(x, a + b) == x * Exp_int(x, a + b - 1);
    Exp_int_mult(x, a - 1, b);
    assert Exp_int(x, a + b - 1) == Exp_int(x, a - 1) * Exp_int(x, b);
    assert Exp_int(x, a) == x * Exp_int(x, a - 1);
  }
}

lemma Str2Int_AllZero(s: string)
  requires ValidBitString(s) && AllZero(s)
  ensures Str2Int(s) == 0
{
  if |s| > 0 {
    assert s[|s|-1] == '0';
    Str2Int_AllZero(s[0..|s|-1]);
  }
}

lemma Str2Int_append_bit(s: string, bit: char)
  requires ValidBitString(s)
  requires bit == '0' || bit == '1'
  ensures Str2Int(s + [bit]) == 2 * Str2Int(s) + (if bit == '1' then 1 else 0)
{
}

method IntToBinaryString(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures |s| > 0
  ensures Str2Int(s) == n
{
  if n == 0 {
    s := "0";
  } else {
    s := "";
    var temp := n;
    while temp > 0
      invariant ValidBitString(s)
      invariant temp == 0 || temp > 0
      decreases temp
    {
      if temp % 2 == 0 {
        s := "0" + s;
      } else {
        s := "1" + s;
      }
      temp := temp / 2;
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
  // Check if sy represents 0
  var is_zero := true;
  var i := 0;
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant is_zero == (forall j | 0 <= j < i :: sy[j] == '0')
  {
    if sy[i] != '0' {
      is_zero := false;
    }
    i := i + 1;
  }
  
  if is_zero {
    // y == 0, so x^0 = 1
    res := "1";
    Str2Int_AllZero(sy);
    Exp_int_zero(Str2Int(sx));
    return;
  }
  
  // Check if sy is even (last bit is 0)
  if sy[|sy|-1] == '0' {
    // y is even: x^y = (x^2)^(y/2)
    var sy_div2 := sy[0..|sy|-1];
    if |sy_div2| == 0 {
      sy_div2 := "0";
    }
    
    var sx_squared := Mul(sx, sx);
    var sx_squared_mod := IntToBinaryString(Str2Int(sx_squared) % Str2Int(sz));
    
    res := ModExp(sx_squared_mod, sy_div2, sz);
    
    assert Str2Int(sy) % 2 == 0;
    assert Str2Int(sy_div2) == Str2Int(sy) / 2;
    Exp_int_even(Str2Int(sx), Str2Int(sy));
    
  } else {
    // y is odd
    if |sy| == 1 && sy[0] == '1' {
      // y == 1, so x^1 = x
      res := IntToBinaryString(Str2Int(sx) % Str2Int(sz));
      assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    } else {
      // y > 1 and odd: x^y = x * x^(y-1)
      var sy_minus1 := sy[0..|sy|-1];
      if |sy_minus1| == 0 {
        sy_minus1 := "0";
      }
      
      var temp := ModExp(sx, sy_minus1, sz);
      var result := Mul(sx, temp);
      res := IntToBinaryString(Str2Int(result) % Str2Int(sz));
      
      assert Str2Int(sy) == Str2Int(sy_minus1) * 2 + 1;
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Str2Int(sx) * Exp_int(Str2Int(sx), Str2Int(sy) - 1);
    }
  }
}
// </vc-code>

