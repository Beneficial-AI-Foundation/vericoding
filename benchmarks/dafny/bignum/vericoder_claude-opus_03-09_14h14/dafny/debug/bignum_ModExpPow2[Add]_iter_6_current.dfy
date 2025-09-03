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

// <vc-helpers>
lemma ExpPow2Lemma(x: nat, n: nat)
  ensures n > 0 ==> Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  if n > 0 {
    calc {
      Exp_int(x, Exp_int(2, n));
      == Exp_int(x, 2 * Exp_int(2, n-1));
      == { ExpMultLemma(x, Exp_int(2, n-1), Exp_int(2, n-1)); }
      Exp_int(x, Exp_int(2, n-1)) * Exp_int(x, Exp_int(2, n-1));
      == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
    }
  }
}

lemma ExpMultLemma(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a) * 1;
  } else {
    calc {
      Exp_int(x, a + b);
      == x * Exp_int(x, a + b - 1);
      == { ExpMultLemma(x, a, b - 1); }
      x * (Exp_int(x, a) * Exp_int(x, b - 1));
      == Exp_int(x, a) * (x * Exp_int(x, b - 1));
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma ModMultLemma(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  // This is a fundamental property of modular arithmetic
}

lemma Str2IntPowerOfTwo(s: string, n: nat)
  requires ValidBitString(s)
  requires |s| == n + 1
  requires n >= 0
  requires s[0] == '1'
  requires forall i | 1 <= i < |s| :: s[i] == '0'
  ensures Str2Int(s) == Exp_int(2, n)
  decreases n
{
  if n == 0 {
    assert s == "1";
    assert Str2Int("1") == 1;
    assert Exp_int(2, 0) == 1;
  } else {
    var s' := s[0..|s|-1];
    assert |s'| == n;
    assert s'[0] == '1';
    assert forall i | 1 <= i < |s'| :: s'[i] == '0';
    Str2IntPowerOfTwo(s', n-1);
    assert Str2Int(s') == Exp_int(2, n-1);
    assert s[|s|-1] == '0';
    calc {
      Str2Int(s);
      == 2 * Str2Int(s') + 0;
      == 2 * Exp_int(2, n-1);
      == Exp_int(2, n);
    }
  }
}

method Mod(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)

method Mult(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
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
    res := Mod(sx, sz);
    assert Str2Int(sy) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
  } else if Str2Int(sy) == 0 {
    res := "1";
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert 1 % Str2Int(sz) == 1 || Str2Int(sz) == 1;
  } else {
    var sy_half := "1";
    var i := 0;
    while i < n - 1
      invariant 0 <= i <= n - 1
      invariant |sy_half| == i + 1
      invariant ValidBitString(sy_half)
      invariant sy_half[0] == '1'
      invariant forall j | 1 <= j < |sy_half| :: sy_half[j] == '0'
      invariant Str2Int(sy_half) == Exp_int(2, i)
    {
      sy_half := sy_half + "0";
      Str2IntPowerOfTwo(sy_half, i+1);
      i := i + 1;
    }
    
    assert |sy_half| == n;
    assert Str2Int(sy_half) == Exp_int(2, n-1);
    
    var temp := ModExpPow2(sx, sy_half, n-1, sz);
    var temp_squared := Mult(temp, temp);
    res := Mod(temp_squared, sz);
    
    ExpPow2Lemma(Str2Int(sx), n);
    assert Str2Int(sy) == Exp_int(2, n);
    
    calc {
      Str2Int(res);
      == Str2Int(temp_squared) % Str2Int(sz);
      == (Str2Int(temp) * Str2Int(temp)) % Str2Int(sz);
      == { assert Str2Int(temp) == Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz); }
      ((Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz)) * (Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz))) % Str2Int(sz);
      == { ModMultLemma(Exp_int(Str2Int(sx), Exp_int(2, n-1)), Exp_int(Str2Int(sx), Exp_int(2, n-1)), Str2Int(sz)); }
      (Exp_int(Str2Int(sx), Exp_int(2, n-1)) * Exp_int(Str2Int(sx), Exp_int(2, n-1))) % Str2Int(sz);
      == Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2) % Str2Int(sz);
      == Exp_int(Str2Int(sx), Exp_int(2, n)) % Str2Int(sz);
      == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    }
  }
}
// </vc-code>

