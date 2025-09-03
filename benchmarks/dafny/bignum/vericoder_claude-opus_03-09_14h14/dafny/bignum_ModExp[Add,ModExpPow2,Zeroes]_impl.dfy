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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Str2IntDivBy2(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s[0..|s|-1]) == Str2Int(s) / 2
{
  // Direct from definition of Str2Int
}

lemma ExpIntProperties(x: nat, y: nat)
  ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, y-1)
  ensures Exp_int(x, 0) == 1
{
  // Direct from definition
}

lemma ModExpBase(x: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, 0) % z == 1 % z
  ensures Exp_int(x, 1) % z == x % z
{
  assert Exp_int(x, 0) == 1;
  assert Exp_int(x, 1) == x;
}

lemma ModMultiplication(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  // Standard modular arithmetic property
}

lemma ExpIntSquare(x: nat, n: nat)
  ensures Exp_int(x, 2*n) == Exp_int(x, n) * Exp_int(x, n)
{
  if n == 0 {
    assert Exp_int(x, 0) == 1;
  } else {
    calc {
      Exp_int(x, 2*n);
      == x * Exp_int(x, 2*n - 1);
      == x * x * Exp_int(x, 2*(n-1));
      == { if n > 1 { ExpIntSquare(x, n-1); } }
      x * x * Exp_int(x, n-1) * Exp_int(x, n-1);
      == x * Exp_int(x, n-1) * x * Exp_int(x, n-1);
      == Exp_int(x, n) * Exp_int(x, n);
    }
  }
}

lemma ModExpEven(x: nat, y: nat, z: nat)
  requires z > 1
  requires y >= 2
  requires y % 2 == 0
  ensures Exp_int(x, y) % z == Exp_int(Exp_int(x, y/2) % z, 2) % z
{
  assert y == 2 * (y/2);
  ExpIntSquare(x, y/2);
  assert Exp_int(x, y) == Exp_int(x, y/2) * Exp_int(x, y/2);
  ModMultiplication(Exp_int(x, y/2), Exp_int(x, y/2), z);
}

lemma ModExpOdd(x: nat, y: nat, z: nat)
  requires z > 1
  requires y >= 2
  requires y % 2 == 1
  ensures Exp_int(x, y) % z == ((x % z) * (Exp_int(Exp_int(x, y/2) % z, 2) % z)) % z
{
  assert y == 2 * (y/2) + 1;
  ExpIntSquare(x, y/2);
  assert Exp_int(x, y) == x * Exp_int(x, y/2) * Exp_int(x, y/2);
  ModMultiplication(x, Exp_int(x, y/2) * Exp_int(x, y/2), z);
  ModMultiplication(Exp_int(x, y/2), Exp_int(x, y/2), z);
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
    res := "1";
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert Str2Int(res) == 1;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  } else if |sy| == 1 && sy[0] == '1' {
    res := sx;
    assert Str2Int(sy) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    assert Str2Int(res) == Str2Int(sx);
    ModExpBase(Str2Int(sx), Str2Int(sz));
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  } else {
    var y_div_2 := sy[0..|sy|-1];
    assert |y_div_2| > 0;
    assert ValidBitString(y_div_2);
    Str2IntDivBy2(sy);
    assert Str2Int(y_div_2) == Str2Int(sy) / 2;
    
    var half_result := ModExp(sx, y_div_2, sz);
    assert Str2Int(half_result) == Exp_int(Str2Int(sx), Str2Int(y_div_2)) % Str2Int(sz);
    
    if sy[|sy|-1] == '0' {
      var two := "10";
      assert Str2Int(two) == 2;
      assert Str2Int(two) == Exp_int(2, 1);
      res := ModExpPow2(half_result, two, 1, sz);
      assert Str2Int(res) == Exp_int(Str2Int(half_result), 2) % Str2Int(sz);
      assert Str2Int(sy) % 2 == 0;
      assert Str2Int(sy) >= 2;
      ModExpEven(Str2Int(sx), Str2Int(sy), Str2Int(sz));
      assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    } else {
      var two := "10";
      var squared := ModExpPow2(half_result, two, 1, sz);
      assert Str2Int(squared) == Exp_int(Str2Int(half_result), 2) % Str2Int(sz);
      var zero_str := Zeros(1);
      assert Str2Int(zero_str) == 0;
      var x_mod := Add(sx, zero_str);
      assert Str2Int(x_mod) == Str2Int(sx);
      res := Add(squared, x_mod);
      assert Str2Int(res) == Str2Int(squared) + Str2Int(x_mod);
      assert Str2Int(sy) % 2 == 1;
      assert Str2Int(sy) >= 2;
      ModExpOdd(Str2Int(sx), Str2Int(sy), Str2Int(sz));
      assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    }
  }
}
// </vc-code>

