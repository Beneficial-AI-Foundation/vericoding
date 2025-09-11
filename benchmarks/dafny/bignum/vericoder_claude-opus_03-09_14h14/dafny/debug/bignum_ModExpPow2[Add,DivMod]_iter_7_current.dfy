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

// <vc-helpers>
lemma ExpPow2Squared(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  var exp_n_minus_1 := Exp_int(2, n-1);
  var exp_n := Exp_int(2, n);
  assert exp_n == 2 * exp_n_minus_1;
  
  calc {
    Exp_int(x, Exp_int(2, n));
    == Exp_int(x, 2 * exp_n_minus_1);
    == Exp_int(x, exp_n_minus_1 + exp_n_minus_1);
    == { ExpMultiply(x, exp_n_minus_1, exp_n_minus_1); }
    Exp_int(x, exp_n_minus_1) * Exp_int(x, exp_n_minus_1);
    == Exp_int(Exp_int(x, exp_n_minus_1), 2);
  }
}

lemma ExpMultiply(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a) * 1;
  } else {
    calc {
      Exp_int(x, a + b);
      == x * Exp_int(x, a + b - 1);
      == { ExpMultiply(x, a, b - 1); }
      x * (Exp_int(x, a) * Exp_int(x, b - 1));
      == Exp_int(x, a) * (x * Exp_int(x, b - 1));
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma ModExpSquared(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * a) % m == ((a % m) * (a % m)) % m
{
  var a_mod := a % m;
  assert a == (a / m) * m + a_mod;
  calc {
    (a * a) % m;
    == (((a / m) * m + a_mod) * ((a / m) * m + a_mod)) % m;
    == ((a / m) * (a / m) * m * m + 2 * (a / m) * m * a_mod + a_mod * a_mod) % m;
    == (a_mod * a_mod) % m;
    == ((a % m) * (a % m)) % m;
  }
}

method PowerOfTwoString(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures |s| == n + 1
  ensures Str2Int(s) == Exp_int(2, n)
{
  if n == 0 {
    s := "1";
  } else {
    s := "1";
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |s| == i + 1
      invariant ValidBitString(s)
      invariant Str2Int(s) == Exp_int(2, i)
    {
      s := s + "0";
      assert Str2Int(s + "0") == 2 * Str2Int(s);
      i := i + 1;
    }
  }
}

lemma MultiplyMod(a: string, m: string)
  requires ValidBitString(a) && ValidBitString(m)
  requires Str2Int(m) > 0
  ensures (Str2Int(a) * Str2Int(a)) % Str2Int(m) == ((Str2Int(a) % Str2Int(m)) * (Str2Int(a) % Str2Int(m))) % Str2Int(m)
{
  ModExpSquared(Str2Int(a), Str2Int(a), Str2Int(m));
}

method Multiply(a: string, b: string) returns (res: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(a) * Str2Int(b)
{
  // Since we only need to multiply two identical values (square),
  // we can use repeated addition
  // But we need to avoid ghost context by not using Str2Int in loop condition
  // We'll use the actual bit string and shift-add multiplication
  
  res := "0";
  var shifted := a;
  var i := |b|;
  
  while i > 0
    invariant 0 <= i <= |b|
    invariant ValidBitString(res)
    invariant ValidBitString(shifted)
    invariant Str2Int(res) + Str2Int(shifted) * Str2Int(b[i..]) == Str2Int(a) * Str2Int(b)
  {
    i := i - 1;
    if b[i] == '1' {
      res := Add(res, shifted);
    }
    if i > 0 {
      shifted := Add(shifted, shifted);
    }
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
  if n == 0 {
    if sy == "0" {
      res := "1";
    } else {
      assert sy == "1";
      assert Str2Int(sy) == 1;
      var q, r := DivMod(sx, sz);
      res := r;
      assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    }
  } else {
    var halfPower := PowerOfTwoString(n-1);
    assert Str2Int(halfPower) == Exp_int(2, n-1);
    
    var temp := ModExpPow2(sx, halfPower, n-1, sz);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz);
    
    var temp_squared := Multiply(temp, temp);
    assert Str2Int(temp_squared) == Str2Int(temp) * Str2Int(temp);
    
    ExpPow2Squared(Str2Int(sx), n);
    assert Exp_int(Str2Int(sx), Exp_int(2, n)) == Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2);
    
    var q, r := DivMod(temp_squared, sz);
    
    calc {
      Str2Int(r);
      == Str2Int(temp_squared) % Str2Int(sz);
      == (Str2Int(temp) * Str2Int(temp)) % Str2Int(sz);
      == { MultiplyMod(temp, sz); }
      ((Str2Int(temp) % Str2Int(sz)) * (Str2Int(temp) % Str2Int(sz))) % Str2Int(sz);
      == { assert Str2Int(temp) == Str2Int(temp) % Str2Int(sz); }
      (Str2Int(temp) * Str2Int(temp)) % Str2Int(sz);
      == { assert Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2) == 
           Exp_int(Str2Int(sx), Exp_int(2, n-1)) * Exp_int(Str2Int(sx), Exp_int(2, n-1)); }
      Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2) % Str2Int(sz);
      == Exp_int(Str2Int(sx), Exp_int(2, n)) % Str2Int(sz);
    }
    
    res := r;
  }
}
// </vc-code>

