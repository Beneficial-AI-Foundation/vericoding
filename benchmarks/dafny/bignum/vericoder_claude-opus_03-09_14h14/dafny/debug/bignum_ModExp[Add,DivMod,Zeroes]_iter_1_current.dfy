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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
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
lemma ExpRecursive(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
  // By definition of Exp_int
}

lemma ExpEven(x: nat, y: nat, z: nat)
  requires y > 0 && y % 2 == 0 && z > 0
  ensures Exp_int(x, y) % z == (Exp_int(x, y/2) * Exp_int(x, y/2)) % z
{
  assert y == 2 * (y/2);
  assert Exp_int(x, y) == Exp_int(x, 2 * (y/2));
  var k := y/2;
  assert Exp_int(x, 2*k) == Exp_int(x, k) * Exp_int(x, k) by {
    if k == 0 {
      assert Exp_int(x, 0) == 1;
      assert Exp_int(x, 2*0) == 1;
    } else {
      var i := k;
      while i > 0 
        invariant 0 <= i <= k
        invariant Exp_int(x, k + (k-i)) == Exp_int(x, k) * Exp_int(x, k-i)
      {
        i := i - 1;
      }
    }
  }
}

lemma Str2IntDecrease(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s[0..|s|-1]) <= Str2Int(s)
{
  assert s == s[0..|s|-1] + [s[|s|-1]];
  assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
  assert Str2Int(s) >= 2 * Str2Int(s[0..|s|-1]);
  assert Str2Int(s[0..|s|-1]) <= Str2Int(s) / 2;
  assert Str2Int(s[0..|s|-1]) <= Str2Int(s);
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
    res := Zeros(1);
    res := res[0..0] + ['1'];
    var _, rem := DivMod(res, sz);
    return rem;
  }
  
  var lastBit := sy[|sy|-1];
  var syDivTwo := sy[0..|sy|-1];
  
  if |syDivTwo| == 0 {
    syDivTwo := Zeros(1);
  }
  
  if lastBit == '0' {
    // y is even: x^y mod z = (x^(y/2) mod z)^2 mod z
    var halfPower := ModExp(sx, syDivTwo, sz);
    var squared := DivMod(halfPower, sz);
    var product := Add(halfPower, halfPower);
    var _, result := DivMod(product, sz);
    
    // Need to compute halfPower * halfPower mod sz
    var temp := Zeros(1);
    var i := 0;
    while i < |halfPower|
      invariant 0 <= i <= |halfPower|
      invariant ValidBitString(temp)
    {
      if halfPower[|halfPower|-1-i] == '1' {
        var shifted := halfPower + Zeros(i);
        temp := Add(temp, shifted);
      }
      i := i + 1;
    }
    var _, finalRes := DivMod(temp, sz);
    res := finalRes;
  } else {
    // y is odd: x^y mod z = (x * x^(y-1) mod z) mod z
    var yMinusOne := syDivTwo + ['0'];
    var powerYMinusOne := ModExp(sx, yMinusOne, sz);
    
    // Compute x * powerYMinusOne mod sz
    var temp := Zeros(1);
    var i := 0;
    while i < |sx|
      invariant 0 <= i <= |sx|
      invariant ValidBitString(temp)
    {
      if sx[|sx|-1-i] == '1' {
        var shifted := powerYMinusOne + Zeros(i);
        temp := Add(temp, shifted);
      }
      i := i + 1;
    }
    var _, finalRes := DivMod(temp, sz);
    res := finalRes;
  }
}
// </vc-code>

