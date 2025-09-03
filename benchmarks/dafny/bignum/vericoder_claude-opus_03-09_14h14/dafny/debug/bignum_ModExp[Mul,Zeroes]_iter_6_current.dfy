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

lemma ModExp_correctness(x: nat, y: nat, z: nat, res: nat)
  requires z > 1 && y > 0
  requires res == Exp_int(x, y) % z
  ensures res == Exp_int(x, y) % z
{
}

ghost predicate IsAllZeros(s: string)
  requires ValidBitString(s)
{
  AllZero(s)
}

ghost function IsOne(s: string): bool
  requires ValidBitString(s)
{
  Str2Int(s) == 1
}

ghost function IsZero(s: string): bool
  requires ValidBitString(s)
{
  Str2Int(s) == 0
}

method IntToBitString(val: nat, size: nat) returns (result: string)
  ensures ValidBitString(result)
  ensures |result| == size
  ensures Str2Int(result) == val % Exp_int(2, size)
{
  result := Zeros(size);
  var temp_val := val;
  var bit_pos := 0;
  
  while bit_pos < size && temp_val > 0
    invariant 0 <= bit_pos <= size
    invariant ValidBitString(result)
    invariant |result| == size
  {
    if temp_val % 2 == 1 {
      result := result[size - 1 - bit_pos := '1'];
    }
    temp_val := temp_val / 2;
    bit_pos := bit_pos + 1;
  }
}

method ComputeMod(dividend_str: string, divisor_str: string) returns (result: string)
  requires ValidBitString(dividend_str) && ValidBitString(divisor_str)
  requires Str2Int(divisor_str) > 0
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(dividend_str) % Str2Int(divisor_str)
{
  var val := Str2Int(dividend_str);
  var z_val := Str2Int(divisor_str);
  
  while val >= z_val
    decreases val
  {
    val := val - z_val;
  }
  
  result := IntToBitString(val, |divisor_str|);
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
  // Check if sy represents 0 (all zeros)
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
    var one := Zeros(1);
    one := one[0 := '1'];
    assert Str2Int(sy) == 0 by { Str2Int_AllZero(sy); }
    return one;
  }
  
  // Check if sy is even (last bit is 0)
  if sy[|sy|-1] == '0' {
    // y is even
    var sy_div2 := sy[0..|sy|-1];
    var sx_squared := Mul(sx, sx);
    var temp := ModExp(sx_squared, sy_div2, sz);
    
    // Prove correctness for even case
    assert Str2Int(sy) % 2 == 0;
    assert Str2Int(sy_div2) == Str2Int(sy) / 2;
    Exp_int_even(Str2Int(sx), Str2Int(sy));
    
    return temp;
  } else {
    // y is odd
    // Check if sy represents 1
    var is_one := true;
    if |sy| == 1 && sy[0] == '1' {
      is_one := true;
    } else {
      is_one := false;
      i := 0;
      while i < |sy| - 1
        invariant 0 <= i <= |sy| - 1
      {
        if sy[i] != '0' {
          is_one := false;
          break;
        }
        i := i + 1;
      }
      if i == |sy| - 1 && sy[|sy|-1] == '1' {
        is_one := true;
      }
    }
    
    if is_one {
      var result := ComputeMod(sx, sz);
      return result;
    } else {
      var sy_minus1 := sy[0..|sy|-1];
      
      // Check if sy_minus1 is empty or all zeros
      var need_padding := false;
      if |sy_minus1| == 0 {
        need_padding := true;
      } else {
        var all_zero := true;
        i := 0;
        while i < |sy_minus1|
          invariant 0 <= i <= |sy_minus1|
          invariant all_zero == (forall j | 0 <= j < i :: sy_minus1[j] == '0')
        {
          if sy_minus1[i] != '0' {
            all_zero := false;
          }
          i := i + 1;
        }
        need_padding := all_zero;
      }
      
      if need_padding {
        sy_minus1 := Zeros(1);
      }
      
      var temp := ModExp(sx, sy_minus1, sz);
      var result := Mul(sx, temp);
      var final_result := ComputeMod(result, sz);
      
      assert Str2Int(sy) == Str2Int(sy_minus1) * 2 + 1;
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Str2Int(sx) * Exp_int(Str2Int(sx), Str2Int(sy) - 1);
      
      return final_result;
    }
  }
}
// </vc-code>

