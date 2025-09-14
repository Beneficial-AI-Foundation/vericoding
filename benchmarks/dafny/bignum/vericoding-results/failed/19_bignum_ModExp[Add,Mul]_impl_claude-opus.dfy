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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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
lemma Str2IntZero()
  ensures Str2Int("0") == 0
{
  assert |"0"| == 1;
  calc == {
    Str2Int("0");
    == { assert "0"[0..0] == ""; }
    2 * Str2Int("") + 0;
    == 
    2 * 0 + 0;
    ==
    0;
  }
}

lemma Str2IntOne()
  ensures Str2Int("1") == 1
{
  assert |"1"| == 1;
  calc == {
    Str2Int("1");
    == { assert "1"[0..0] == ""; }
    2 * Str2Int("") + 1;
    == 
    2 * 0 + 1;
    ==
    1;
  }
}

lemma ExpIntProperties(x: nat, y: nat)
  ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, y - 1)
  ensures y == 0 ==> Exp_int(x, y) == 1
{
  if y == 0 {
    assert Exp_int(x, y) == 1;
  } else {
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
  }
}

lemma ExpIntEven(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
  decreases y
{
  if y == 2 {
    calc == {
      Exp_int(x, 2);
      == x * Exp_int(x, 1);
      == x * x * Exp_int(x, 0);
      == x * x * 1;
      == x * x;
      == Exp_int(x * x, 1);
    }
  } else {
    calc == {
      Exp_int(x, y);
      == x * Exp_int(x, y - 1);
      == x * x * Exp_int(x, y - 2);
      == { ExpIntEven(x, y - 2); }
      x * x * Exp_int(x * x, (y - 2) / 2);
      == { assert (y - 2) / 2 == y / 2 - 1; }
      x * x * Exp_int(x * x, y / 2 - 1);
      == Exp_int(x * x, y / 2);
    }
  }
}

lemma ModExpCorrectness(x: nat, y: nat, z: nat, result: nat)
  requires z > 1
  requires result == Exp_int(x, y) % z
  ensures result < z
{}

lemma Str2IntPrefix(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures ValidBitString(s[0..|s|-1])
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{}

method Int2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "0";
    Str2IntZero();
  } else {
    var half := n / 2;
    var bit := if n % 2 == 0 then '0' else '1';
    var prefix := Int2Str(half);
    s := prefix + [bit];
    
    assert ValidBitString(prefix);
    var s' := prefix + [bit];
    assert |s'| == |prefix| + 1;
    assert s'[0..|s'|-1] == prefix;
    assert s'[|s'|-1] == bit;
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if bit == '1' then 1 else 0);
    assert Str2Int(s) == 2 * half + n % 2;
    assert n == 2 * half + n % 2;
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
    Str2IntZero();
    ExpIntProperties(Str2Int(sx), 0);
    assert Exp_int(Str2Int(sx), 0) == 1;
    res := Int2Str(1 % Str2Int(sz));
    assert Str2Int(res) == 1 % Str2Int(sz);
  } else if sy == "1" {
    Str2IntOne();
    ExpIntProperties(Str2Int(sx), 1);
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    res := Int2Str(Str2Int(sx) % Str2Int(sz));
  } else {
    var lastChar := sy[|sy| - 1];
    var sy_prefix := sy[0..|sy| - 1];
    
    Str2IntPrefix(sy);
    assert ValidBitString(sy_prefix);
    assert |sy_prefix| < |sy|;
    assert |sy_prefix| > 0;
    
    if lastChar == '0' {
      assert Str2Int(sy) == 2 * Str2Int(sy_prefix);
      ExpIntEven(Str2Int(sx), Str2Int(sy));
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy_prefix));
      
      var x_squared_mod := Int2Str((Str2Int(sx) * Str2Int(sx)) % Str2Int(sz));
      res := ModExp(x_squared_mod, sy_prefix, sz);
      
      assert Str2Int(res) == Exp_int(Str2Int(x_squared_mod), Str2Int(sy_prefix)) % Str2Int(sz);
      assert Str2Int(x_squared_mod) == (Str2Int(sx) * Str2Int(sx)) % Str2Int(sz);
    } else {
      assert lastChar == '1';
      assert Str2Int(sy) == 2 * Str2Int(sy_prefix) + 1;
      assert Str2Int(sy) > 0;
      ExpIntProperties(Str2Int(sx), Str2Int(sy));
      
      var sy_minus_one := Int2Str(Str2Int(sy) - 1);
      var temp := ModExp(sx, sy_minus_one, sz);
      res := Int2Str((Str2Int(sx) * Str2Int(temp)) % Str2Int(sz));
      
      assert Str2Int(temp) == Exp_int(Str2Int(sx), Str2Int(sy) - 1) % Str2Int(sz);
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Str2Int(sx) * Exp_int(Str2Int(sx), Str2Int(sy) - 1);
    }
  }
}
// </vc-code>

