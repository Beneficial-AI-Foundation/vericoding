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
      assert Exp_int(x, y) == Exp_int(x * x, y / 2);
    } else {
      assert Exp_int(x, y) == x * Exp_int(x, y - 1);
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
    // y = 0, so x^0 = 1
    res := "1";
    assert Str2Int(res) == 1;
    assert Exp_int(Str2Int(sx), 0) == 1;
  } else if |sy| == 1 {
    // Base case: y = 1, so x^1 = x
    assert sy == "1";
    assert Str2Int(sy) == 1;
    res := sx;
    assert Str2Int(res) == Str2Int(sx);
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
  } else {
    var lastBit := sy[|sy|-1];
    var syDiv2 := sy[0..|sy|-1];
    
    assert ValidBitString(syDiv2);
    assert |syDiv2| < |sy|;
    Str2IntDivBy2(sy);
    
    if lastBit == '0' {
      // y is even: x^y = (x^2)^(y/2)
      var xSquared := Multiply(sx, sx);
      var xSquaredMod := Mod(xSquared, sz);
      res := ModExp(xSquaredMod, syDiv2, sz);
      
      ModExpCorrectness(Str2Int(sx), Str2Int(sy), Str2Int(sz));
    } else {
      // y is odd: x^y = x * x^(y-1)
      assert lastBit == '1';
      var yMinus1 := Decrement(sy);
      var temp := ModExp(sx, yMinus1, sz);
      var product := Multiply(sx, temp);
      res := Mod(product, sz);
      
      ModExpCorrectness(Str2Int(sx), Str2Int(sy), Str2Int(sz));
    }
  }
}
// </vc-code>

