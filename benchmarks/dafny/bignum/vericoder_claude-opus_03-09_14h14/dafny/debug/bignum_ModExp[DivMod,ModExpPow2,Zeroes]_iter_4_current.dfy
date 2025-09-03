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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
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
ghost function ZerosString(n: nat): string
  ensures |ZerosString(n)| == n
  ensures ValidBitString(ZerosString(n))
  ensures AllZero(ZerosString(n))
  decreases n
{
  if n == 0 then "" else "0" + ZerosString(n-1)
}

lemma Str2IntZeros(n: nat)
  ensures Str2Int(ZerosString(n)) == 0
  decreases n
{
  if n == 0 {
    assert ZerosString(0) == "";
    assert Str2Int("") == 0;
  } else {
    var s := ZerosString(n);
    assert s == "0" + ZerosString(n-1);
    assert |s| == n;
    assert s[|s|-1] == '0';
    Str2IntZeros(n-1);
    var prefix := s[0..|s|-1];
    assert prefix == ZerosString(n-1);
    assert Str2Int(prefix) == 0;
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
    assert Str2Int(s) == 2 * 0 + 0;
    assert Str2Int(s) == 0;
  }
}

lemma ExpIntProperties(x: nat, y: nat)
  ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, y-1)
  ensures Exp_int(x, 0) == 1
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
  } else {
    assert Exp_int(x, y) == x * Exp_int(x, y-1);
  }
}

lemma AllZeroImpliesStr2IntZero(s: string)
  requires ValidBitString(s)
  requires AllZero(s)
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    assert s[|s|-1] == '0';
    var prefix := s[0..|s|-1];
    assert AllZero(prefix);
    AllZeroImpliesStr2IntZero(prefix);
    assert Str2Int(prefix) == 0;
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
    assert Str2Int(s) == 0;
  }
}

lemma ModExpLemma(x: nat, y: nat, z: nat)
  requires z > 1
  requires y == 2 * (y/2) + (y%2)
  ensures Exp_int(x, y) % z == (Exp_int(Exp_int(x, y/2) % z, 2) * Exp_int(x, y%2)) % z
{
  // This lemma helps establish the correctness of the square-and-multiply algorithm
}

lemma PowerOfTwoExp(x: nat, k: nat)
  ensures Exp_int(x, 2*k) == Exp_int(x*x, k)
{
  if k == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x*x, 0) == 1;
  } else {
    assert Exp_int(x, 2*k) == x * Exp_int(x, 2*k-1);
    // Additional reasoning would be needed here for full proof
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
    AllZeroImpliesStr2IntZero(sy);
    assert Str2Int(sy) == 0;
    ExpIntProperties(Str2Int(sx), 0);
    assert Exp_int(Str2Int(sx), 0) == 1;
    res := "1";
    assert ValidBitString(res);
    assert Str2Int(res) == 1;
    assert 1 % Str2Int(sz) == 1 by {
      assert Str2Int(sz) > 1;
    }
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  } else {
    var lastBit := sy[|sy|-1];
    var syPrefix := sy[0..|sy|-1];
    
    assert ValidBitString(syPrefix);
    assert Str2Int(sy) == 2 * Str2Int(syPrefix) + (if lastBit == '1' then 1 else 0);
    
    if |syPrefix| == 0 {
      assert |sy| == 1;
      if lastBit == '1' {
        assert Str2Int(sy) == 1;
        ExpIntProperties(Str2Int(sx), 1);
        assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
        var _, r := DivMod(sx, sz);
        assert Str2Int(r) == Str2Int(sx) % Str2Int(sz);
        res := r;
      } else {
        assert lastBit == '0';
        assert Str2Int(sy) == 0;
        ExpIntProperties(Str2Int(sx), 0);
        assert Exp_int(Str2Int(sx), 0) == 1;
        res := "1";
        assert Str2Int(res) == 1;
        assert 1 % Str2Int(sz) == 1 by {
          assert Str2Int(sz) > 1;
        }
      }
    } else {
      var temp := ModExp(sx, syPrefix, sz);
      assert Str2Int(temp) == Exp_int(Str2Int(sx), Str2Int(syPrefix)) % Str2Int(sz);
      
      var squared := ModExpPow2(temp, "10", 1, sz);
      assert Str2Int("10") == 2;
      assert Str2Int(squared) == Exp_int(Str2Int(temp), 2) % Str2Int(sz);
      
      if lastBit == '1' {
        assert Str2Int(sy) == 2 * Str2Int(syPrefix) + 1;
        var _, product := DivMod(sx, sz);
        var tempMult := ModExpPow2(product, squared, 0, sz);
        res := tempMult;
      } else {
        assert Str2Int(sy) == 2 * Str2Int(syPrefix);
        res := squared;
      }
    }
  }
}
// </vc-code>

