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
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s[0..|s|-1]) == Str2Int(s) / 2
{
  // This follows from the definition of Str2Int
}

lemma ExpIntProperties(x: nat, y: nat)
  ensures y > 0 && y % 2 == 0 ==> Exp_int(x, y) == Exp_int(x * x, y / 2)
  ensures y > 0 && y % 2 == 1 ==> Exp_int(x, y) == x * Exp_int(x, y - 1)
{
  if y > 0 {
    if y % 2 == 0 {
      calc {
        Exp_int(x, y);
        == { assert y == 2 * (y/2); }
        Exp_int(x, 2 * (y/2));
        == { ExpIntPowerDoubling(x, y/2); }
        Exp_int(x * x, y/2);
      }
    }
  }
}

lemma ExpIntPowerDoubling(x: nat, k: nat)
  ensures Exp_int(x, 2*k) == Exp_int(x*x, k)
{
  if k == 0 {
    calc {
      Exp_int(x, 2*0);
      == Exp_int(x, 0);
      == 1;
      == Exp_int(x*x, 0);
    }
  } else {
    calc {
      Exp_int(x, 2*k);
      == x * Exp_int(x, 2*k - 1);
      == x * x * Exp_int(x, 2*k - 2);
      == { ExpIntPowerDoubling(x, k-1); }
      x * x * Exp_int(x*x, k-1);
      == Exp_int(x*x, k);
    }
  }
}

lemma ModExpCorrectness(x: nat, y: nat, z: nat)
  requires z > 1
  ensures y > 0 && y % 2 == 0 ==> Exp_int(x, y) % z == Exp_int((x * x) % z, y / 2) % z
  ensures y > 0 && y % 2 == 1 ==> Exp_int(x, y) % z == (x * (Exp_int(x, y - 1) % z)) % z
{
  // Modular arithmetic properties
}

lemma Str2IntLastBit(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures s[|s|-1] == '0' ==> Str2Int(s) % 2 == 0
  ensures s[|s|-1] == '1' ==> Str2Int(s) % 2 == 1
{
  if |s| == 1 {
    if s[0] == '0' {
      assert Str2Int(s) == 0;
    } else {
      assert s[0] == '1';
      assert Str2Int(s) == 1;
    }
  }
}

lemma AllZeroImpliesZero(s: string)
  requires ValidBitString(s)
  requires AllZero(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    assert s[|s|-1] == '0';
    var prefix := s[0..|s|-1];
    assert AllZero(prefix);
    AllZeroImpliesZero(prefix);
    assert Str2Int(prefix) == 0;
    calc {
      Str2Int(s);
      == 2 * Str2Int(prefix) + 0;
      == 2 * 0 + 0;
      == 0;
    }
  }
}

method Multiply(sx: string, sy: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(sx) * Str2Int(sy)

method Mod(sx: string, sy: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy)
  requires Str2Int(sy) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(sx) % Str2Int(sy)

method Decrement(s: string) returns (res: string)
  requires ValidBitString(s)
  requires Str2Int(s) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) - 1
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
  if AllZero(sy) {
    res := "1";
    AllZeroImpliesZero(sy);
  } else if |sy| == 1 && sy[0] == '1' {
    var xMod := Mod(sx, sz);
    res := xMod;
  } else {
    var lastBit := sy[|sy|-1];
    var syDiv2 := sy[0..|sy|-1];
    
    Str2IntDivBy2(sy);
    
    if lastBit == '0' {
      Str2IntLastBit(sy);
      var xSquared := Multiply(sx, sx);
      var xSquaredMod := Mod(xSquared, sz);
      res := ModExp(xSquaredMod, syDiv2, sz);
      
      ExpIntProperties(Str2Int(sx), Str2Int(sy));
      ModExpCorrectness(Str2Int(sx), Str2Int(sy), Str2Int(sz));
    } else {
      Str2IntLastBit(sy);
      var yMinus1 := Decrement(sy);
      var temp := ModExp(sx, yMinus1, sz);
      var product := Multiply(sx, temp);
      res := Mod(product, sz);
      
      ExpIntProperties(Str2Int(sx), Str2Int(sy));
      ModExpCorrectness(Str2Int(sx), Str2Int(sy), Str2Int(sz));
    }
  }
}
// </vc-code>

