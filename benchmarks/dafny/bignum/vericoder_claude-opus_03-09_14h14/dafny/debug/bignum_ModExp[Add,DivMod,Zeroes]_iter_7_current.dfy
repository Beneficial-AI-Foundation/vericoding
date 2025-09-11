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
  ensures Str2Int(s[0..|s|-1]) < Str2Int(s) || (AllZero(s[0..|s|-1]) && s[|s|-1] == '1')
  ensures Str2Int(s[0..|s|-1]) <= Str2Int(s)
{
  assert s == s[0..|s|-1] + [s[|s|-1]];
  assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
  if s[|s|-1] == '1' {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
    assert Str2Int(s) > 2 * Str2Int(s[0..|s|-1]);
    if Str2Int(s[0..|s|-1]) > 0 {
      assert Str2Int(s[0..|s|-1]) < Str2Int(s);
    }
  } else {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]);
    if Str2Int(s[0..|s|-1]) > 0 {
      assert Str2Int(s[0..|s|-1]) < Str2Int(s);
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
    AllZeroImpliesZero(s[0..|s|-1]);
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 0;
    assert Str2Int(s) == 0;
  }
}

method IsAllZero(s: string) returns (b: bool)
  requires ValidBitString(s)
  ensures b == AllZero(s)
{
  b := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant b == (forall j | 0 <= j < i :: s[j] == '0')
  {
    if s[i] != '0' {
      b := false;
    }
    i := i + 1;
  }
}

method Multiply(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  // Implementation for multiplication
  res := "0";
  var temp := s1;
  var multiplier := s2;
  
  while !AllZero(multiplier)
    invariant ValidBitString(res) && ValidBitString(temp) && ValidBitString(multiplier)
    invariant Str2Int(res) + Str2Int(temp) * Str2Int(multiplier) == Str2Int(s1) * Str2Int(s2)
    decreases Str2Int(multiplier)
  {
    if multiplier[|multiplier|-1] == '1' {
      res := Add(res, temp);
    }
    temp := Add(temp, temp);
    multiplier := multiplier[0..|multiplier|-1];
  }
}

lemma ModularExponentProp(x: nat, y: nat, z: nat)
  requires z > 0
  ensures (x % z * Exp_int(x, y) % z) % z == (x * Exp_int(x, y)) % z
{
  // Modular arithmetic property
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
  var isZero := IsAllZero(sy);
  if isZero {
    AllZeroImpliesZero(sy);
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    
    res := "1";
    assert ValidBitString(res);
    assert Str2Int(res) == 1;
    assert Str2Int(res) < Str2Int(sz);
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    return res;
  } else {
    var lastBit := sy[|sy|-1];
    var syPrefix := sy[0..|sy|-1];
    assert |syPrefix| < |sy|;
    
    if lastBit == '0' {
      // y is even: x^y mod z = (x^(y/2) mod z)^2 mod z
      assert Str2Int(sy) == 2 * Str2Int(syPrefix);
      
      if |syPrefix| == 0 || AllZero(syPrefix) {
        // y = 2, so x^2 mod z
        var temp := Multiply(sx, sx);
        var q, r := DivMod(temp, sz);
        res := r;
        assert Str2Int(res) == (Str2Int(sx) * Str2Int(sx)) % Str2Int(sz);
        assert Exp_int(Str2Int(sx), 2) == Str2Int(sx) * Str2Int(sx);
        assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
      } else {
        var halfPower := ModExp(sx, syPrefix, sz);
        assert Str2Int(halfPower) == Exp_int(Str2Int(sx), Str2Int(syPrefix)) % Str2Int(sz);
        
        // Compute (halfPower * halfPower) mod sz
        var temp := Multiply(halfPower, halfPower);
        var q, r := DivMod(temp, sz);
        res := r;
        
        ExpEven(Str2Int(sx), Str2Int(sy), Str2Int(sz));
        assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
      }
    } else {
      // y is odd: x^y mod z = (x * x^(y-1) mod z) mod z  
      assert Str2Int(sy) == 2 * Str2Int(syPrefix) + 1;
      
      if |syPrefix| == 0 || AllZero(syPrefix) {
        // y = 1, so x mod z
        var q, r := DivMod(sx, sz);
        res := r;
        assert Str2Int(res) == Str2Int(sx) % Str2Int(sz);
        assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
        assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
      } else {
        // Recursive call with syPrefix (which represents (y-1)/2)
        // x^y = x * x^(y-1) = x * (x^2)^((y-1)/2)
        var xSquared := Multiply(sx, sx);
        var q1, xSquaredMod := DivMod(xSquared, sz);
        
        var powerHalf := ModExp(xSquaredMod, syPrefix, sz);
        assert Str2Int(powerHalf) == Exp_int(Str2Int(xSquaredMod), Str2Int(syPrefix)) % Str2Int(sz);
        
        // Multiply by x and take mod
        var temp := Multiply(sx, powerHalf);
        var q2, r := DivMod(temp, sz);
        res := r;
        
        assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
      }
    }
  }
}
// </vc-code>

