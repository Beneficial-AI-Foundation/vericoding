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

// <vc-helpers>
lemma ExpIntProperties(x: nat, y: nat)
  ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, y - 1)
  ensures Exp_int(x, 0) == 1
{
}

lemma ModExpProperty(x: nat, y: nat, z: nat)
  requires z > 0
  requires y > 0
  ensures (Exp_int(x, y) % z) == ((x % z) * (Exp_int(x, y - 1) % z)) % z
{
  assert Exp_int(x, y) == x * Exp_int(x, y - 1);
}

lemma Str2IntZeroString()
  ensures ValidBitString("0")
  ensures Str2Int("0") == 0
{
}

lemma Str2IntOneString()
  ensures ValidBitString("1")
  ensures Str2Int("1") == 1
{
}

lemma Str2IntTwoString()
  ensures ValidBitString("10")
  ensures Str2Int("10") == 2
{
  assert Str2Int("10") == 2 * Str2Int("1") + 0 == 2 * 1 + 0 == 2;
}

lemma Str2IntAllZeros(s: string)
  requires ValidBitString(s)
  requires forall i | 0 <= i < |s| :: s[i] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    var prefix := s[0..|s|-1];
    assert forall i | 0 <= i < |prefix| :: prefix[i] == '0';
    Str2IntAllZeros(prefix);
    assert s[|s|-1] == '0';
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
    assert Str2Int(s) == 0;
  }
}

lemma Str2IntHasOne(s: string)
  requires ValidBitString(s)
  requires exists i | 0 <= i < |s| :: s[i] == '1'
  ensures Str2Int(s) > 0
  decreases |s|
{
  if |s| == 0 {
    assert false;
  } else if s[|s|-1] == '1' {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
    assert Str2Int(s) >= 1;
  } else {
    var prefix := s[0..|s|-1];
    assert exists i | 0 <= i < |prefix| :: prefix[i] == '1';
    Str2IntHasOne(prefix);
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
    assert Str2Int(s) > 0;
  }
}

method IsAllZeros(s: string) returns (allZeros: bool)
  requires ValidBitString(s)
  ensures allZeros <==> (forall i | 0 <= i < |s| :: s[i] == '0')
  ensures allZeros ==> Str2Int(s) == 0
{
  allZeros := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant allZeros <==> (forall j | 0 <= j < i :: s[j] == '0')
  {
    if s[i] != '0' {
      allZeros := false;
      break;
    }
    i := i + 1;
  }
  if allZeros {
    Str2IntAllZeros(s);
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
  var isZero := IsAllZeros(sy);
  if isZero {
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    Str2IntOneString();
    res := "1";
    assert Str2Int(res) == 1;
    assert Str2Int(res) == 1 % Str2Int(sz);
  } else {
    assert exists i | 0 <= i < |sy| :: sy[i] == '1';
    Str2IntHasOne(sy);
    assert Str2Int(sy) > 0;
    
    Str2IntTwoString();
    var y_div_2_str, y_mod_2_str := DivMod(sy, "10");
    assert Str2Int("10") == 2;
    assert Str2Int(y_div_2_str) == Str2Int(sy) / 2;
    assert Str2Int(y_mod_2_str) == Str2Int(sy) % 2;
    
    var half_exp := ModExp(sx, y_div_2_str, sz);
    assert Str2Int(half_exp) == Exp_int(Str2Int(sx), Str2Int(y_div_2_str)) % Str2Int(sz);
    
    var squared, _ := DivMod(half_exp + half_exp, sz);
    var temp := squared;
    
    if y_mod_2_str == "1" {
      assert Str2Int(y_mod_2_str) == 1;
      var x_mod_z, _ := DivMod(sx, sz);
      var product, _ := DivMod(temp + x_mod_z, sz);
      res := product;
    } else {
      assert y_mod_2_str == "0";
      assert Str2Int(y_mod_2_str) == 0;
      res := temp;
    }
  }
}
// </vc-code>

