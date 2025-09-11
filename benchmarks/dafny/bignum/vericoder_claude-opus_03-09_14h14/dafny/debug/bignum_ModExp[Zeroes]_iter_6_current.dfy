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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Exp_int_positive(x: nat, y: nat)
  requires x > 0
  ensures Exp_int(x, y) > 0
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
  } else {
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    Exp_int_positive(x, y - 1);
  }
}

lemma Str2Int_nonnegative(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) >= 0
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    Str2Int_nonnegative(s[0..|s|-1]);
  }
}

lemma Str2Int_AllZero_is_Zero(s: string)
  requires ValidBitString(s)
  requires AllZero(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    assert s[|s|-1] == '0';
    Str2Int_AllZero_is_Zero(s[0..|s|-1]);
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 0;
  }
}

method Int2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  if n == 0 {
    s := "0";
  } else {
    var quotient := n / 2;
    var remainder := n % 2;
    var prefix := Int2Str(quotient);
    var digit := if remainder == 1 then "1" else "0";
    s := prefix + digit;
  }
}

method ModuloStr(x: nat, z: nat) returns (res: string)
  requires z > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == x % z
{
  var modResult := x % z;
  res := Int2Str(modResult);
}

method MultiplyMod(x: nat, y: nat, z: nat) returns (res: string)
  requires z > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (x * y) % z
{
  var product := x * y;
  res := ModuloStr(product, z);
}

method ComputeStr2Int(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  if |s| == 0 {
    n := 0;
  } else {
    var prefix := s[0..|s|-1];
    var prefixInt := ComputeStr2Int(prefix);
    var lastBit := if s[|s|-1] == '1' then 1 else 0;
    n := 2 * prefixInt + lastBit;
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
  if |sy| == 0 || AllZero(sy) {
    Str2Int_AllZero_is_Zero(sy);
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    var z_int := ComputeStr2Int(sz);
    res := Int2Str(1 % z_int);
    assert Str2Int(res) == 1 % Str2Int(sz);
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  } else if sy == "1" {
    assert Str2Int(sy) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    var x_int := ComputeStr2Int(sx);
    var z_int := ComputeStr2Int(sz);
    res := ModuloStr(x_int, z_int);
    assert Str2Int(res) == Str2Int(sx) % Str2Int(sz);
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  } else {
    var lastChar := sy[|sy|-1];
    if lastChar == '0' {
      // y is even: x^y = (x^(y/2))^2
      var sy_half := sy[0..|sy|-1];
      assert Str2Int(sy) == 2 * Str2Int(sy_half);
      var half_result := ModExp(sx, sy_half, sz);
      var half_int := ComputeStr2Int(half_result);
      var z_int := ComputeStr2Int(sz);
      assert half_int == Exp_int(Str2Int(sx), Str2Int(sy_half)) % Str2Int(sz);
      res := MultiplyMod(half_int, half_int, z_int);
      assert Str2Int(res) == (half_int * half_int) % Str2Int(sz);
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx), 2 * Str2Int(sy_half));
    } else {
      // y is odd: x^y = x * x^(y-1)
      var sy_minus_1_str := sy[0..|sy|-1] + "0";
      assert Str2Int(sy) == 2 * Str2Int(sy[0..|sy|-1]) + 1;
      assert Str2Int(sy_minus_1_str) == Str2Int(sy) - 1;
      var rec_result := ModExp(sx, sy_minus_1_str, sz);
      var rec_int := ComputeStr2Int(rec_result);
      var x_int := ComputeStr2Int(sx);
      var z_int := ComputeStr2Int(sz);
      assert rec_int == Exp_int(Str2Int(sx), Str2Int(sy) - 1) % Str2Int(sz);
      res := MultiplyMod(x_int, rec_int, z_int);
      assert Str2Int(res) == (Str2Int(sx) * rec_int) % Str2Int(sz);
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Str2Int(sx) * Exp_int(Str2Int(sx), Str2Int(sy) - 1);
    }
  }
}
// </vc-code>

