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
lemma ExpIntAdd(x: nat, y: nat, z: nat)
  ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
{
  if y == 0 {
    assert Exp_int(x, y + z) == Exp_int(x, z);
    assert Exp_int(x, y) * Exp_int(x, z) == 1 * Exp_int(x, z) == Exp_int(x, z);
  } else {
    ExpIntAdd(x, y - 1, z);
  }
}

lemma ExpIntMod(x: nat, y: nat, z: nat)
  requires z > 0
  ensures (Exp_int(x, y) % z) == ((Exp_int(x, y / 2) % z) * (Exp_int(x, y / 2) % z) * (if y % 2 == 1 then x % z else 1)) % z
{
  if y == 0 {
    assert Exp_int(x, y) == 1;
  } else if y == 1 {
    assert Exp_int(x, y) == x;
    assert y / 2 == 0;
    assert Exp_int(x, y / 2) == 1;
  } else {
    var half := y / 2;
    var rem := y % 2;
    assert y == 2 * half + rem;
    ExpIntAdd(x, half, half + rem);
    assert Exp_int(x, y) == Exp_int(x, half) * Exp_int(x, half + rem);
    if rem == 0 {
      assert Exp_int(x, half + rem) == Exp_int(x, half);
    } else {
      assert rem == 1;
      assert Exp_int(x, half + 1) == x * Exp_int(x, half);
    }
  }
}

lemma Str2IntZeros(s: string)
  requires AllZero(s)
  requires ValidBitString(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
  } else {
    assert s[|s|-1] == '0';
    assert forall i | 0 <= i < |s|-1 :: s[0..|s|-1][i] == s[i] == '0';
    Str2IntZeros(s[0..|s|-1]);
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
    assert sy[0] == '0' || sy[0] == '1';
    if sy[0] == '0' {
      assert Str2Int(sy) == 0;
      assert Exp_int(Str2Int(sx), 0) == 1;
      var one := "1";
      assert Str2Int(one) == 1;
      return one;
    } else {
      assert sy[0] == '1';
      assert Str2Int(sy) == 1;
      assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
      
      var zeros := Zeros(|sz|);
      var temp := Add(sx, zeros);
      
      assert Str2Int(zeros) == 0;
      assert Str2Int(temp) == Str2Int(sx);
      
      var modRes := ModExpPow2(temp, "1", 0, sz);
      assert Str2Int("1") == 1 == Exp_int(2, 0);
      assert Str2Int(modRes) == Exp_int(Str2Int(temp), 1) % Str2Int(sz);
      assert Str2Int(modRes) == Str2Int(sx) % Str2Int(sz);
      return modRes;
    }
  }
  
  var halfY := sy[0..|sy|-1];
  assert ValidBitString(halfY);
  assert |halfY| == |sy| - 1 < |sy|;
  
  var halfRes := ModExp(sx, halfY, sz);
  assert Str2Int(halfRes) == Exp_int(Str2Int(sx), Str2Int(halfY)) % Str2Int(sz);
  
  var squared := Mul(halfRes, halfRes);
  
  if sy[|sy|-1] == '1' {
    assert Str2Int(sy) == 2 * Str2Int(halfY) + 1;
    var withX := Mul(squared, sx);
    
    var zeros := Zeros(|sz|);
    var temp := Add(withX, zeros);
    assert Str2Int(temp) == Str2Int(withX);
    
    var n := |sz| - 1;
    var pow2 := Zeros(n + 1);
    pow2 := pow2[0..n] + "1";
    assert |pow2| == n + 1;
    assert Str2Int(pow2) == Exp_int(2, n);
    
    res := ModExpPow2(temp, pow2, n, sz);
    assert Str2Int(res) == Exp_int(Str2Int(temp), Exp_int(2, n)) % Str2Int(sz);
    assert Str2Int(res) == (Str2Int(withX) % Str2Int(sz));
    
    ExpIntMod(Str2Int(sx), Str2Int(sy), Str2Int(sz));
  } else {
    assert sy[|sy|-1] == '0';
    assert Str2Int(sy) == 2 * Str2Int(halfY);
    
    var zeros := Zeros(|sz|);
    var temp := Add(squared, zeros);
    assert Str2Int(temp) == Str2Int(squared);
    
    var n := |sz| - 1;
    var pow2 := Zeros(n + 1);
    pow2 := pow2[0..n] + "1";
    assert |pow2| == n + 1;
    assert Str2Int(pow2) == Exp_int(2, n);
    
    res := ModExpPow2(temp, pow2, n, sz);
    assert Str2Int(res) == Exp_int(Str2Int(temp), Exp_int(2, n)) % Str2Int(sz);
    assert Str2Int(res) == (Str2Int(squared) % Str2Int(sz));
    
    ExpIntMod(Str2Int(sx), Str2Int(sy), Str2Int(sz));
  }
}
// </vc-code>

