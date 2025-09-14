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

// <vc-helpers>
lemma {:induction false} ExpLemma(x: nat, y: nat, z: nat)
  ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
{
  if z == 0 {
    assert Exp_int(x, y + 0) == Exp_int(x, y) * 1;
  } else {
    ExpLemma(x, y, z - 1);
    assert Exp_int(x, y + z) == x * Exp_int(x, y + z - 1);
    assert Exp_int(x, y) * Exp_int(x, z) == Exp_int(x, y) * (x * Exp_int(x, z - 1));
  }
}

lemma ModLemma(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  calc {
    (a * b) % m;
    == ((a % m) * b) % m;
    == ((a % m) * (b % m)) % m;
  }
}

lemma ModExpLemma(base: nat, exp: nat, m: nat)
  requires m > 1
  ensures Exp_int(base, exp) % m == Exp_int(base % m, exp) % m
  decreases exp
{
  if exp == 0 {
    assert Exp_int(base, 0) % m == 1 % m;
    assert Exp_int(base % m, 0) % m == 1 % m;
  } else {
    ModExpLemma(base, exp - 1, m);
    calc {
      Exp_int(base, exp) % m;
      == (base * Exp_int(base, exp - 1)) % m;
      == ((base % m) * (Exp_int(base, exp - 1) % m)) % m; 
        {ModLemma(base, Exp_int(base, exp - 1), m);}
      == ((base % m) * (Exp_int(base % m, exp - 1) % m)) % m;
      == Exp_int(base % m, exp) % m;
    }
  }
}

lemma ExpPow2Lemma(n: nat)
  ensures Exp_int(2, n) == if n == 0 then 1 else 2 * Exp_int(2, n - 1)
{
  if n > 0 {
    ExpPow2Lemma(n - 1);
  }
}

lemma Str2IntLengthLemma(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) < Exp_int(2, |s|)
  decreases s
{
  if |s| == 0 {
    assert Str2Int(s) < 1;
  } else {
    var prefix := s[0..|s|-1];
    Str2IntLengthLemma(prefix);
    ExpPow2Lemma(|s|-1);
    if s[|s|-1] == '1' {
      calc {
        Str2Int(s);
        == 2 * Str2Int(prefix) + 1;
        < 2 * Exp_int(2, |s|-1) + 1;
        <= 2 * Exp_int(2, |s|-1);
        == Exp_int(2, |s|);
      }
    } else {
      calc {
        Str2Int(s);
        == 2 * Str2Int(prefix) + 0;
        < 2 * Exp_int(2, |s|-1);
        == Exp_int(2, |s|);
      }
    }
  }
}

lemma BitStringZeroLemma(s: string)
  requires ValidBitString(s)
  ensures (|s| == 0) == (Str2Int(s) == 0)
  decreases s
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    BitStringZeroLemma(s[0..|s|-1]);
    if s[|s|-1] == '0' {
      assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 0;
    } else {
      assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
      assert Str2Int(s) != 0;
    }
  }
}

lemma ModExpPow2Lemma(base: nat, exp_power: nat, m: nat)
  requires m > 1
  ensures Exp_int(base, Exp_int(2, exp_power)) % m == Exp_int(Exp_int(base, Exp_int(2, exp_power - 1)) % m, 2) % m when exp_power > 0
{
  if exp_power > 0 {
    calc {
      Exp_int(base, Exp_int(2, exp_power)) % m;
      == Exp_int(base, 2 * Exp_int(2, exp_power - 1)) % m;
      == Exp_int(Exp_int(base, Exp_int(2, exp_power - 1)), 2) % m;
      == Exp_int(Exp_int(base, Exp_int(2, exp_power - 1)) % m, 2) % m;
        {ModExpLemma(Exp_int(base, Exp_int(2, exp_power - 1)), 2, m);}
    }
  }
}

lemma ExpIntOne(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma ModExpRecursionLemma(base: nat, exp: nat, m: nat)
  requires m > 1
  ensures Exp_int(base, exp) % m == Exp_int(Exp_int(base, exp/2) % m, 2) % m * (if exp % 2 == 1 then base % m else 1) % m
  decreases exp
{
  if exp == 0 {
    assert Exp_int(base, 0) % m == 1 % m;
  } else if exp == 1 {
    assert Exp_int(base, 1) % m == base % m;
  } else {
    ModExpRecursionLemma(base, exp/2, m);
  }
}

lemma StringSliceLemma(s: string, n: int)
  requires 0 <= n <= |s|
  ensures |s[0..n]| == n
{
}

lemma StringConcatLemma(s1: string, s2: string)
  ensures |s1 + s2| == |s1| + |s2|
{
}

lemma ModExpPow2Helper(sx: string, n: nat, sz: string)
  requires ValidBitString(sx) && ValidBitString(sz)
  requires Str2Int(sz) > 1
  ensures ValidBitString(ModExpPow2(sx, "1", n, sz))
  ensures Str2Int(ModExpPow2(sx, "1", n, sz)) == Exp_int(Str2Int(sx), Exp_int(2, n)) % Str2Int(sz)
  decreases n
{
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
  if |sy| == 1 {
    if sy[0] == '0' {
      res := "1";
    } else {
      var mod_base := ModExpPow2(sx, "1", 0, sz);
      res := mod_base;
    }
  } else {
    var half := sy[0..|sy|-1];
    var mod_half := ModExp(sx, half, sz);
    
    var temp_str := "10";
    var mod_squared := ModExpPow2(mod_half, temp_str, 1, sz);
    
    if sy[|sy|-1] == '1' {
      var mod_base := ModExpPow2(sx, "1", 0, sz);
      var temp := Mul(mod_squared, mod_base);
      res := ModExpPow2(temp, "1", 0, sz);
    } else {
      res := mod_squared;
    }
  }
}
// </vc-code>

