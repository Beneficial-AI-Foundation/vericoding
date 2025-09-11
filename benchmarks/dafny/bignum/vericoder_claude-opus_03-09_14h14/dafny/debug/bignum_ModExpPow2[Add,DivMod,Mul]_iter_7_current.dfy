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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Exp_int_2_is_square(x: nat)
  ensures Exp_int(x, 2) == x * x
{
  calc == {
    Exp_int(x, 2);
    x * Exp_int(x, 1);
    x * (x * Exp_int(x, 0));
    x * (x * 1);
    x * x;
  }
}

lemma Exp_int_pow2_square(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  if n == 1 {
    assert Exp_int(2, 1) == 2;
    assert Exp_int(2, 0) == 1;
    Exp_int_2_is_square(x);
    assert Exp_int(x, 2) == x * x;
    assert Exp_int(x, 1) == x;
    Exp_int_2_is_square(x);
  } else {
    calc == {
      Exp_int(x, Exp_int(2, n));
      Exp_int(x, 2 * Exp_int(2, n-1));
      { Exp_int_power_double(x, Exp_int(2, n-1)); }
      Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
    }
  }
}

lemma Exp_int_power_double(x: nat, k: nat)
  ensures Exp_int(x, 2*k) == Exp_int(Exp_int(x, k), 2)
{
  if k == 0 {
    assert Exp_int(x, 0) == 1;
    Exp_int_2_is_square(1);
    assert Exp_int(1, 2) == 1;
  } else {
    calc == {
      Exp_int(x, 2*k);
      x * Exp_int(x, 2*k - 1);
      x * Exp_int(x, k + (k-1));
      { Exp_int_add(x, k, k-1); }
      x * (Exp_int(x, k) * Exp_int(x, k-1));
      (Exp_int(x, k) * x) * Exp_int(x, k-1);
      Exp_int(x, k) * (x * Exp_int(x, k-1));
      Exp_int(x, k) * Exp_int(x, k);
      { Exp_int_2_is_square(Exp_int(x, k)); }
      Exp_int(Exp_int(x, k), 2);
    }
  }
}

lemma Exp_int_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if b == 0 {
    assert Exp_int(x, b) == 1;
  } else {
    calc == {
      Exp_int(x, a + b);
      x * Exp_int(x, a + b - 1);
      x * Exp_int(x, a + (b - 1));
      { Exp_int_add(x, a, b - 1); }
      x * (Exp_int(x, a) * Exp_int(x, b - 1));
      Exp_int(x, a) * (x * Exp_int(x, b - 1));
      Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma Str2Int_leading_zero(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
  decreases |s|
{
  if |s| == 1 {
    assert s == "0";
    assert Str2Int(s) == 0;
    assert s[1..] == "";
    assert Str2Int("") == 0;
  } else {
    calc == {
      Str2Int(s);
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      { assert s[0..|s|-1] == "0" + s[1..|s|-1]; }
      2 * Str2Int("0" + s[1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      { 
        assert |"0" + s[1..|s|-1]| < |s|;
        Str2Int_leading_zero("0" + s[1..|s|-1]); 
      }
      2 * Str2Int(s[1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      { assert s[1..] == s[1..|s|-1] + [s[|s|-1]]; }
      Str2Int(s[1..]);
    }
  }
}

lemma Str2Int_all_zeros(s: string)
  requires ValidBitString(s)
  requires forall i | 0 <= i < |s| :: s[i] == '0'
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    assert s[|s|-1] == '0';
    var prefix := s[0..|s|-1];
    assert forall i | 0 <= i < |prefix| :: prefix[i] == '0';
    Str2Int_all_zeros(prefix);
    calc == {
      Str2Int(s);
      2 * Str2Int(prefix) + 0;
      2 * 0 + 0;
      0;
    }
  }
}

lemma Str2Int_power_of_2_representation(sy: string, n: nat)
  requires ValidBitString(sy)
  requires |sy| == n + 1
  requires sy[0] == '1'
  requires forall i | 1 <= i < |sy| :: sy[i] == '0'
  ensures Str2Int(sy) == Exp_int(2, n)
{
  if n == 0 {
    assert |sy| == 1;
    assert sy == "1";
    assert Str2Int("1") == 1;
    assert Exp_int(2, 0) == 1;
  } else {
    var prefix := sy[0..|sy|-1];
    assert |prefix| == n;
    assert prefix[0] == '1';
    assert forall i | 1 <= i < |prefix| :: prefix[i] == '0';
    Str2Int_power_of_2_representation(prefix, n-1);
    assert Str2Int(prefix) == Exp_int(2, n-1);
    assert sy[|sy|-1] == '0';
    calc == {
      Str2Int(sy);
      2 * Str2Int(prefix) + 0;
      2 * Exp_int(2, n-1);
      Exp_int(2, n);
    }
  }
}

lemma ModExpCorrectness(x: nat, y: nat, z: nat, r: nat)
  requires z > 1
  requires r == (x % z) * (x % z) % z
  ensures r == (x * x) % z
{
  // This follows from modular arithmetic properties
}

function BuildPowerOf2String(n: nat): string
  ensures ValidBitString(BuildPowerOf2String(n))
  ensures |BuildPowerOf2String(n)| == n + 1
  ensures BuildPowerOf2String(n)[0] == '1'
  ensures forall i | 1 <= i < |BuildPowerOf2String(n)| :: BuildPowerOf2String(n)[i] == '0'
  ensures Str2Int(BuildPowerOf2String(n)) == Exp_int(2, n)
{
  var s := "1" + seq(n, i => '0');
  Str2Int_power_of_2_representation(s, n);
  s
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
    assert |sy| == 1;
    if sy == "0" {
      assert Str2Int(sy) == 0;
      assert Exp_int(Str2Int(sx), 0) == 1;
      var _, rem := DivMod("1", sz);
      return rem;
    } else {
      assert sy == "1";
      assert Str2Int(sy) == 1;
      assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
      var _, rem := DivMod(sx, sz);
      return rem;
    }
  } else {
    if sy[0] == '0' {
      assert forall i | 1 <= i < |sy| :: sy[i] == '0' by {
        if !(forall i | 1 <= i < |sy| :: sy[i] == '0') {
          var j :| 1 <= j < |sy| && sy[j] == '1';
          var sy_suffix := sy[1..];
          assert |sy_suffix| == n;
          Str2Int_leading_zero(sy);
          assert Str2Int(sy) == Str2Int(sy_suffix);
          assert sy_suffix[j-1] == '1';
          assert Str2Int(sy_suffix) >= Exp_int(2, n-j);
          assert n-j >= 0;
          assert Exp_int(2, 0) == 1;
          assert Str2Int(sy_suffix) >= 1;
          assert Str2Int(sy) >= 1;
          assert Str2Int(sy) != 0;
          assert false;
        }
      }
      Str2Int_all_zeros(sy);
      assert Str2Int(sy) == 0;
      assert Exp_int(Str2Int(sx), 0) == 1;
      var _, rem := DivMod("1", sz);
      return rem;
    } else {
      assert sy[0] == '1';
      assert forall i | 1 <= i < |sy| :: sy[i] == '0' by {
        Str2Int_power_of_2_representation(sy, n);
      }
      
      var sy_half := BuildPowerOf2String(n-1);
      assert |sy_half| == n;
      assert Str2Int(sy_half) == Exp_int(2, n-1);
      
      var temp := ModExpPow2(sx, sy_half, n-1, sz);
      var temp_squared := Mul(temp, temp);
      
      Exp_int_pow2_square(Str2Int(sx), n);
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Exp_int(Str2Int(sx), Str2Int(sy_half)), 2);
      assert Str2Int(temp_squared) == Str2Int(temp) * Str2Int(temp);
      assert Str2Int(temp) == Exp_int(Str2Int(sx), Str2Int(sy_half)) % Str2Int(sz);
      
      Exp_int_2_is_square(Exp_int(Str2Int(sx), Str2Int(sy_half)));
      ModExpCorrectness(Exp_int(Str2Int(sx), Str2Int(sy_half)), 
                        Exp_int(Str2Int(sx), Str2Int(sy_half)), 
                        Str2Int(sz), 
                        Str2Int(temp_squared) % Str2Int(sz));
      
      var _, result := DivMod(temp_squared, sz);
      return result;
    }
  }
}
// </vc-code>

