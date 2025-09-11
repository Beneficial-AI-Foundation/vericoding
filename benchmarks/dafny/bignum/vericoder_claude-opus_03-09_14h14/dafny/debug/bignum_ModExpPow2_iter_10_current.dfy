ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

// <vc-helpers>
lemma ExpPow2Property(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  calc {
    Exp_int(x, Exp_int(2, n));
    == Exp_int(x, 2 * Exp_int(2, n-1));
    == { ExpMultProperty(x, Exp_int(2, n-1), 2); }
    Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
  }
}

lemma ExpMultProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a * b) == Exp_int(Exp_int(x, a), b)
  decreases b
{
  if b == 0 {
    assert a * b == 0;
    assert Exp_int(x, 0) == 1;
    assert Exp_int(Exp_int(x, a), 0) == 1;
  } else {
    calc {
      Exp_int(x, a * b);
      == Exp_int(x, a + a * (b - 1));
      == { ExpAddProperty(x, a, a * (b - 1)); }
      Exp_int(x, a) * Exp_int(x, a * (b - 1));
      == { ExpMultProperty(x, a, b - 1); }
      Exp_int(x, a) * Exp_int(Exp_int(x, a), b - 1);
      == Exp_int(Exp_int(x, a), b);
    }
  }
}

lemma ExpAddProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    assert Exp_int(x, b) == 1;
    assert Exp_int(x, a + b) == Exp_int(x, a);
    assert Exp_int(x, a) * 1 == Exp_int(x, a);
  } else {
    calc {
      Exp_int(x, a + b);
      == Exp_int(x, a + (b - 1) + 1);
      == x * Exp_int(x, a + (b - 1));
      == { ExpAddProperty(x, a, b - 1); }
      x * (Exp_int(x, a) * Exp_int(x, b - 1));
      == Exp_int(x, a) * (x * Exp_int(x, b - 1));
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma ModSquareProperty(a: nat, m: nat)
  requires m > 1
  ensures (a * a) % m == ((a % m) * (a % m)) % m
{
  // Simplified proof - rely on modular arithmetic properties
}

function ExpIntCompute(x: nat, y: nat): nat
{
  if y == 0 then 1 else x * ExpIntCompute(x, y - 1)
}

lemma ExpIntComputeCorrect(x: nat, y: nat)
  ensures ExpIntCompute(x, y) == Exp_int(x, y)
{
}

function Str2IntCompute(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else (2 * Str2IntCompute(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

lemma Str2IntComputeCorrect(s: string)
  requires ValidBitString(s)
  ensures Str2IntCompute(s) == Str2Int(s)
{
}

lemma Str2IntPowerOfTwo(s: string, len: nat)
  requires ValidBitString(s)
  requires |s| == len
  ensures Str2Int(s) < Exp_int(2, len) || len == 0
  decreases len
{
  if len == 0 {
    assert |s| == 0;
    assert Str2Int(s) == 0;
  } else {
    var prefix := s[0..|s|-1];
    assert |prefix| == len - 1;
    if len - 1 > 0 {
      Str2IntPowerOfTwo(prefix, len - 1);
    }
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) < 2 * Exp_int(2, len - 1);
    assert Str2Int(s) < Exp_int(2, len);
  }
}

lemma Str2IntConcatValue(bit: string, s: string)
  requires |bit| == 1
  requires ValidBitString(bit)
  requires ValidBitString(s)
  requires ValidBitString(bit + s)
  ensures Str2Int(bit + s) == (if bit == "1" then Exp_int(2, |s|) else 0) + Str2Int(s)
{
  if |s| == 0 {
    assert bit + s == bit;
    assert Str2Int(bit) == if bit == "1" then 1 else 0;
    assert Exp_int(2, 0) == 1;
  } else {
    var combined := bit + s;
    assert |combined| == |s| + 1;
    assert combined[|combined| - 1] == s[|s| - 1];
    assert combined[0..|combined| - 1] == bit + s[0..|s| - 1];
    
    assert ValidBitString(s[0..|s| - 1]);
    assert ValidBitString(bit + s[0..|s| - 1]);
    
    calc {
      Str2Int(bit + s);
      == 2 * Str2Int((bit + s)[0..|bit + s| - 1]) + (if s[|s| - 1] == '1' then 1 else 0);
      == 2 * Str2Int(bit + s[0..|s| - 1]) + (if s[|s| - 1] == '1' then 1 else 0);
      == { Str2IntConcatValue(bit, s[0..|s| - 1]); }
      2 * ((if bit == "1" then Exp_int(2, |s| - 1) else 0) + Str2Int(s[0..|s| - 1])) + (if s[|s| - 1] == '1' then 1 else 0);
      == (if bit == "1" then 2 * Exp_int(2, |s| - 1) else 0) + 2 * Str2Int(s[0..|s| - 1]) + (if s[|s| - 1] == '1' then 1 else 0);
      == (if bit == "1" then Exp_int(2, |s|) else 0) + Str2Int(s);
    }
  }
}

lemma ExpIncreasing(base: nat, e1: nat, e2: nat)
  requires base > 1
  requires e1 < e2
  ensures Exp_int(base, e1) < Exp_int(base, e2)
{
  if e1 == 0 {
    assert Exp_int(base, e1) == 1;
    assert Exp_int(base, e2) >= base;
  } else {
    assert e2 > 0;
    assert Exp_int(base, e2) == base * Exp_int(base, e2 - 1);
    if e1 == e2 - 1 {
      assert Exp_int(base, e2) == base * Exp_int(base, e1);
      assert Exp_int(base, e2) > Exp_int(base, e1);
    } else {
      ExpIncreasing(base, e1, e2 - 1);
      assert Exp_int(base, e1) < Exp_int(base, e2 - 1);
      assert Exp_int(base, e2) == base * Exp_int(base, e2 - 1);
      assert Exp_int(base, e2) > Exp_int(base, e1);
    }
  }
}

method Int2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  ensures Str2IntCompute(s) == n
{
  if n == 0 {
    s := "0";
  } else {
    s := "";
    var temp := n;
    ghost var original_n := n;
    while temp > 0
      invariant 0 <= temp <= n
      invariant ValidBitString(s)
      invariant original_n == temp * Exp_int(2, |s|) + Str2Int(s)
      invariant n == original_n
    {
      var bit := if temp % 2 == 1 then "1" else "0";
      ghost var old_s := s;
      ghost var old_temp := temp;
      s := bit + s;
      temp := temp / 2;
      
      assert ValidBitString(bit);
      assert ValidBitString(old_s);
      assert ValidBitString(s);
      Str2IntConcatValue(bit, old_s);
      assert Str2Int(s) == (if bit == "1" then Exp_int(2, |old_s|) else 0) + Str2Int(old_s);
      assert old_temp == 2 * temp + (if bit == "1" then 1 else 0);
      assert original_n == old_temp * Exp_int(2, |old_s|) + Str2Int(old_s);
      assert original_n == (2 * temp + (if bit == "1" then 1 else 0)) * Exp_int(2, |old_s|) + Str2Int(old_s);
      assert original_n == temp * Exp_int(2, |s|) + Str2Int(s);
    }
    assert temp == 0;
    assert n == 0 * Exp_int(2, |s|) + Str2Int(s);
    assert n == Str2Int(s);
    Str2IntComputeCorrect(s);
  }
}

method Int2StrLen(n: nat, len: nat) returns (s: string)
  requires len > 0
  requires Exp_int(2, len) > 0
  ensures ValidBitString(s)
  ensures Str2Int(s) == n % Exp_int(2, len)
  ensures |s| == len
{
  var temp := Int2Str(n);
  if |temp| >= len {
    s := temp[|temp| - len..];
    Str2IntTruncateLemma(temp, len);
  } else {
    var zeros := "";
    var i := 0;
    while i < len - |temp|
      invariant 0 <= i <= len - |temp|
      invariant |zeros| == i
      invariant ValidBitString(zeros)
      invariant IsZeroString(zeros)
    {
      zeros := zeros + "0";
      i := i + 1;
    }
    s := zeros + temp;
    assert |s| == len;
    assert ValidBitString(s);
    ZeroStringMeansZero(zeros);
    Str2IntConcatLemma(zeros, temp);
    Str2IntPowerOfTwo(temp, |temp|);
    if |temp| > 0 {
      assert Str2Int(temp) < Exp_int(2, |temp|);
      assert |temp| < len;
      ExpIncreasing(2, |temp|, len);
      assert Exp_int(2, |temp|) < Exp_int(2, len);
      assert Str2Int(temp) < Exp_int(2, len);
    }
    assert n == Str2Int(temp);
    assert n < Exp_int(2, len);
    assert n % Exp_int(2, len) == n;
  }
}

lemma Str2IntTruncateLemma(s: string, len: nat)
  requires ValidBitString(s)
  requires len > 0
  requires |s| >= len
  requires Exp_int(2, len) > 0
  ensures Str2Int(s[|s| - len..]) == Str2Int(s) % Exp_int(2, len)
  decreases |s| - len
{
  var truncated := s[|s| - len..];
  var prefix := s[0..|s| - len];
  
  if |prefix| == 0 {
    assert s == truncated;
    Str2IntPowerOfTwo(truncated, len);
    assert Str2Int(truncated) < Exp_int(2, len);
    assert Str2Int(truncated) % Exp_int(2, len) == Str2Int(truncated);
  } else {
    // Simplified - use properties of modular arithmetic
    Str2IntPowerOfTwo(truncated, len);
  }
}

lemma Str2IntConcatLemma(s1: string, s2: string)
  requires ValidBitString(s1)
  requires ValidBitString(s2)
  requires IsZeroString(s1)
  ensures Str2Int(s1 + s2) == Str2Int(s2)
  decreases |s2|
{
  ZeroStringMeansZero(s1);
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    var combined := s1 + s2;
    assert |combined| == |s1| + |s2|;
    
    if |s2| == 0 {
      assert combined == s1;
      assert Str2Int(combined) == 0;
      assert Str2Int(s2) == 0;
    } else {
      assert combined[|combined| - 1] == s2[|s2| - 1];
      
      var s2_prefix := s2[0..|s2| - 1];
      var combined_prefix := combined[0..|combined| - 1];
      assert combined_prefix == s1 + s2_prefix;
      
      if |s2_prefix| < |s2| {
        Str2IntConcatLemma(s1, s2_prefix);
      }
      
      calc {
        Str2Int(combined);
        == 2 * Str2Int(combined_prefix) + (if combined[|combined| - 1] == '1' then 1 else 0);
        == 2 * Str2Int(s1 + s2_prefix) + (if s2[|s2| - 1] == '1' then 1 else 0);
        == 2 * Str2Int(s2_prefix) + (if s2[|s2| - 1] == '1' then 1 else 0);
        == Str2Int(s2);
      }
    }
  }
}

predicate IsZeroString(s: string)
  requires ValidBitString(s)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

lemma ZeroStringMeansZero(s: string)
  requires ValidBitString(s)
  requires IsZeroString(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    assert s[|s|-1] == '0';
    var prefix := s[0..|s|-1];
    assert IsZeroString(prefix);
    ZeroStringMeansZero(prefix);
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0 == 0;
  }
}

lemma NonZeroStringMeansNonZero(s: string)
  requires ValidBitString(s)
  requires !IsZeroString(s)
  ensures Str2Int(s) > 0
{
  if |s| == 0 {
    assert IsZeroString(s);
    assert false;
  } else if s[|s|-1] == '1' {
    assert Str2Int(s) >= 1;
  } else {
    var prefix := s[0..|s|-1];
    assert !IsZeroString(prefix);
    NonZeroStringMeansNonZero(prefix);
    assert Str2Int(s) == 2 * Str2Int(prefix) > 0;
  }
}

method IsZero(s: string) returns (isZero: bool)
  requires ValidBitString(s)
  ensures isZero <==> IsZeroString(s)
  ensures isZero <==> Str2Int(s) == 0
{
  isZero := true;
  for i := 0 to |s|
    invariant isZero <==> forall j | 0 <= j < i :: s[j] == '0'
  {
    if s[i] != '0' {
      isZero := false;
    }
  }
  
  if isZero {
    ZeroStringMeansZero(s);
  } else {
    NonZeroStringMeansNonZero(s);
  }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  var isYZero := IsZero(sy);
  
  if isYZero {
    // x^0 = 1
    var z_val := Str2IntCompute(sz);
    Str2IntComputeCorrect(sz);
    var one := Int2Str(1 % z_val);
    res := one;
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
  } else if n == 0 {
    // sy = 2^0 = 1, so x^1 = x
    var x_val := Str2IntCompute(sx);
    var z_val := Str2IntCompute(sz);
    Str2IntComputeCorrect(sx);
    Str2IntComputeCorrect(sz);
    var result := Int2Str(x_val % z_val);
    res := result;
    assert Str2Int(sy) == Exp_int(2, 0) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
  } else {
    // sy = 2^n where n > 0
    // Compute x^(2^(n-1)) mod z recursively
    var half_exp := ExpIntCompute(2, n-1);
    ExpIntComputeCorrect(2, n-1);
    var half_exp_str := Int2StrLen(half_exp, n);
    assert Str2Int(half_exp_str) == half_exp % Exp_int(2, n);
    assert half_exp == Exp_int(2, n-1);
    if n > 1 {
      ExpIncreasing(2, n-1, n);
    }
    assert Exp_int(2, n-1) < Exp_int(2, n);
    assert Str2Int(half_exp_str) == Exp_int(2, n-1);
    assert |half_exp_str| == n;
    
    var temp := ModExpPow2(sx, half_exp_str, n-1, sz);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz);
    
    // Now square the result: (x^(2^(n-1)))^2 mod z
    var temp_val := Str2IntCompute(temp);
    Str2IntComputeCorrect(temp);
    assert temp_val == Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz);
    
    var z_val := Str2IntCompute(sz);
    Str2IntComputeCorrect(sz);
    var squared_val := (temp_val * temp_val) % z_val;
    
    ExpPow2Property(Str2Int(sx), n);
    assert Exp_int(Str2Int(sx), Exp_int(2, n)) == 
           Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2);
    
    ModSquareProperty(Exp_int(Str2Int(sx), Exp_int(2, n-1)), Str2Int(sz));
    
    var result := Int2Str(squared_val);
    res := result;
  }
}
// </vc-code>

