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
lemma ExpIntZero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma ExpIntOne(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma ExpIntDistributive(x: nat, y: nat, z: nat)
  ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
{
  if y == 0 {
    assert Exp_int(x, y + z) == Exp_int(x, z);
    assert Exp_int(x, y) * Exp_int(x, z) == 1 * Exp_int(x, z) == Exp_int(x, z);
  } else {
    ExpIntDistributive(x, y - 1, z);
  }
}

lemma ModExpPow2Properties(n: nat)
  ensures Exp_int(2, n) > 0
{
  if n == 0 {
    assert Exp_int(2, 0) == 1;
  } else {
    ModExpPow2Properties(n - 1);
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
    AllZeroImpliesZero(s[0..|s|-1]);
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 0;
    assert Str2Int(s) == 2 * 0 + 0 == 0;
  }
}

lemma PowerOfTwoString(n: nat, s: string)
  requires |s| == n
  requires ValidBitString(s)
  requires AllZero(s)
  ensures ValidBitString("1" + s)
  ensures Str2Int("1" + s) == Exp_int(2, n)
{
  AllZeroImpliesZero(s);
  assert Str2Int(s) == 0;
  
  var powerStr := "1" + s;
  assert |powerStr| == n + 1;
  
  if n == 0 {
    assert powerStr == "1";
    assert Str2Int("1") == 1;
    assert Exp_int(2, 0) == 1;
  } else {
    assert powerStr[|powerStr|-1] == s[n-1];
    assert s[n-1] == '0';
    assert powerStr[|powerStr|-1] == '0';
    var prefix := powerStr[0..|powerStr|-1];
    assert prefix == "1" + s[0..|s|-1];
    assert AllZero(s[0..|s|-1]);
    PowerOfTwoString(n-1, s[0..|s|-1]);
    assert Str2Int(prefix) == Exp_int(2, n-1);
    assert Str2Int(powerStr) == 2 * Str2Int(prefix) + 0;
    assert Str2Int(powerStr) == 2 * Exp_int(2, n-1);
    assert 2 * Exp_int(2, n-1) == Exp_int(2, n);
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
  if AllZero(sy) {
    AllZeroImpliesZero(sy);
    res := "1";
    ExpIntZero(Str2Int(sx));
  } else if |sy| == 1 {
    if sy == "0" {
      res := "1";
      ExpIntZero(Str2Int(sx));
    } else {
      assert sy == "1";
      res := sx;
      ExpIntOne(Str2Int(sx));
      assert Str2Int(res) < Str2Int(sz) || Str2Int(res) >= Str2Int(sz);
      if Str2Int(res) >= Str2Int(sz) {
        var temp := ModExpPow2(sx, "1", 0, sz);
        res := temp;
      }
    }
  } else {
    var n := |sy| - 1;
    var powerOfTwo := Zeros(n);
    PowerOfTwoString(n, powerOfTwo);
    powerOfTwo := "1" + powerOfTwo;
    
    var highPart := ModExpPow2(sx, powerOfTwo, n, sz);
    
    var remainderStr := sy[1..];
    assert |remainderStr| > 0;
    
    var lowPart := ModExp(sx, remainderStr, sz);
    
    if sy[0] == '1' {
      var temp := Mul(highPart, lowPart);
      res := ModExpPow2(temp, "1", 0, sz);
      ExpIntDistributive(Str2Int(sx), Exp_int(2, n), Str2Int(remainderStr));
    } else {
      res := lowPart;
    }
  }
}
// </vc-code>

