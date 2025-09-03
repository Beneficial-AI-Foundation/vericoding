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

// <vc-helpers>
lemma Str2IntZero()
  ensures Str2Int("0") == 0
{
}

lemma Str2IntOne()
  ensures Str2Int("1") == 1
{
}

lemma ExpIntZero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma ExpIntOne(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma Str2IntRecursive(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
}

lemma ExpIntRecursive(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma Str2IntYDiv2(sy: string)
  requires ValidBitString(sy)
  requires |sy| > 1
  ensures sy[|sy|-1] == '0' ==> Str2Int(sy[0..|sy|-1]) == Str2Int(sy) / 2
  ensures sy[|sy|-1] == '1' ==> Str2Int(sy[0..|sy|-1]) == (Str2Int(sy) - 1) / 2
{
  Str2IntRecursive(sy);
  var lastBit := if sy[|sy|-1] == '1' then 1 else 0;
  assert Str2Int(sy) == 2 * Str2Int(sy[0..|sy|-1]) + lastBit;
}

lemma ModExpPow2Property(x: nat, n: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, Exp_int(2, n)) % z == Exp_int(x % z, Exp_int(2, n)) % z
{
}

lemma ModExpIdentity(x: nat, y: nat, z: nat)
  requires z > 1
  requires y > 0
  ensures Exp_int(x, y) % z == ((Exp_int(x, y/2) % z) * (Exp_int(x, y/2) % z) * (if y % 2 == 1 then x % z else 1)) % z
{
}

lemma ExpIntPowerRelation(x: nat, y: nat)
  requires y > 0
  ensures y % 2 == 0 ==> Exp_int(x, y) == Exp_int(x, y/2) * Exp_int(x, y/2)
  ensures y % 2 == 1 ==> Exp_int(x, y) == x * Exp_int(x, y/2) * Exp_int(x, y/2)
{
  if y % 2 == 0 {
    assert y == 2 * (y/2);
    assert Exp_int(x, y) == Exp_int(x, 2 * (y/2));
  } else {
    assert y == 2 * (y/2) + 1;
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    assert Exp_int(x, y - 1) == Exp_int(x, 2 * (y/2));
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
  if |sy| == 1 {
    if sy[0] == '0' {
      res := "1";
      Str2IntOne();
      ExpIntZero(Str2Int(sx));
      assert Str2Int(sy) == 0;
    } else {
      res := sx;
      var x := Str2Int(sx);
      var z := Str2Int(sz);
      Str2IntOne();
      ExpIntOne(x);
      assert Str2Int(sy) == 1;
      assert Exp_int(x, 1) == x;
      
      var temp := ModExpPow2(sx, "1", 0, sz);
      res := temp;
    }
  } else {
    var lastBit := sy[|sy|-1];
    var syDiv2 := sy[0..|sy|-1];
    
    assert ValidBitString(syDiv2);
    assert |syDiv2| < |sy|;
    assert |syDiv2| > 0;
    
    var halfPower := ModExp(sx, syDiv2, sz);
    
    Str2IntYDiv2(sy);
    
    var x := Str2Int(sx);
    var y := Str2Int(sy);
    var z := Str2Int(sz);
    var hp := Str2Int(halfPower);
    
    assert hp == Exp_int(x, Str2Int(syDiv2)) % z;
    
    var squared := ModExpPow2(halfPower, "10", 1, sz);
    
    if lastBit == '1' {
      assert y == 2 * Str2Int(syDiv2) + 1;
      ExpIntPowerRelation(x, y);
      ModExpIdentity(x, y, z);
      
      var modX := ModExpPow2(sx, "1", 0, sz);
      res := Add(Add(squared, modX), "0");
      res := ModExpPow2(res, "1", 0, sz);
    } else {
      assert y == 2 * Str2Int(syDiv2);
      ExpIntPowerRelation(x, y);
      res := squared;
    }
  }
}
// </vc-code>

