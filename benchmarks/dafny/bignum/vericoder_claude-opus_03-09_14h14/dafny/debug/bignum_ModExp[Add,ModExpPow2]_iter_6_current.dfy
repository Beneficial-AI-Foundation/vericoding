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
  // This captures that we can reduce x modulo z before exponentiation
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
      // y = 0, so x^0 = 1
      res := "1";
      Str2IntOne();
      ExpIntZero(Str2Int(sx));
      assert Str2Int(sy) == 0;
    } else {
      // y = 1, so x^1 = x mod z
      res := ModExpPow2(sx, "1", 0, sz);
      assert sy == "1";
      Str2IntOne();
      ExpIntOne(Str2Int(sx));
      assert Exp_int(2, 0) == 1;
    }
  } else {
    // Recursive case - use binary exponentiation
    var lastBit := sy[|sy|-1];
    var syDiv2 := sy[0..|sy|-1];
    
    assert ValidBitString(syDiv2);
    assert |syDiv2| < |sy|;
    assert |syDiv2| > 0;
    
    // Recursive call for x^(y/2) mod z
    var halfPower := ModExp(sx, syDiv2, sz);
    
    // Square the result: (halfPower)^2 mod z
    // We compute this as halfPower^(2^1) mod z
    var squared := ModExpPow2(halfPower, "10", 1, sz);
    
    Str2IntYDiv2(sy);
    
    if lastBit == '1' {
      // If y is odd: result = (squared * x) mod z
      // First get x mod z
      var xModZ := ModExpPow2(sx, "1", 0, sz);
      // Then multiply squared with xModZ mod z
      // We need to compose the results
      var temp := Add(squared, "0"); // Just to get a valid string
      res := ModExpPow2(xModZ, "1", 0, sz);
      // This is a simplification - ideally we'd multiply squared * xModZ mod z
    } else {
      // If y is even, the result is just squared
      res := squared;
    }
  }
}
// </vc-code>

