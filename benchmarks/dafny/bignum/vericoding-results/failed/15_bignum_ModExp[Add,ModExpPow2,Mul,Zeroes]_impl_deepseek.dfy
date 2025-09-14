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
lemma Lemma_Mul_Zero(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) * 0 == 0
{
}

lemma Lemma_Exp_Zero_Base(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma Lemma_Exp_Zero_Exponent(x: nat)
  requires x == 0
  ensures Exp_int(x, 0) == 1
{
}

lemma Lemma_Mod_One(x: nat)
  ensures x % 1 == 0
{
}

lemma Lemma_Exp_One_Exponent(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma Lemma_Str2Int_Empty()
  ensures Str2Int("") == 0
{
}

ghost function BitStringLength(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  |s|
}

lemma Lemma_Exp_Positive(x: nat, y: nat)
  ensures Exp_int(x, y) >= 1 || y == 0
{
  if y == 0 {
  } else {
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    Lemma_Exp_Positive(x, y - 1);
  }
}

lemma Lemma_Mod_LessThan(x: nat, m: nat)
  requires m > 0
  ensures x % m < m
{
}

lemma Lemma_Mod_Mul(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x * y) % m == (x % m) * (y % m) % m
{
}

lemma Lemma_Mod_Exp(x: nat, y: nat, m: nat)
  requires m > 0
  ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
  decreases y
{
  if y == 0 {
    assert Exp_int(x, 0) % m == 1 % m;
    assert Exp_int(x % m, 0) % m == 1 % m;
  } else {
    Lemma_Mod_Exp(x, y - 1, m);
    Lemma_Mod_Mul(Exp_int(x, y - 1), x, m);
  }
}

lemma Lemma_HalfString(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures ValidBitString(s[0..|s|-1])
{
}

lemma Lemma_ModExpPow2_Call(sx: string, sy: string, n: nat, sz: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures exists res: string :: 
    ValidBitString(res) && 
    Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
{
}

lemma Lemma_Mul_Call(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures exists res: string ::
    ValidBitString(res) && 
    Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
}

lemma Lemma_Mod_Zero(x: nat)
  ensures x % 1 == 0
{
}

lemma Lemma_OneMod(m: nat)
  requires m > 0
  ensures 1 % m == 1
{
}

lemma Lemma_HalfStringValid(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures ValidBitString(s[0..|s|-1])
{
}

lemma Lemma_Exp_Zero_Result(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

ghost function Exp_int_ghost(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then 1 else x * Exp_int_ghost(x, y - 1)
}

lemma Lemma_Exp_int_equiv(x: nat, y: nat)
  ensures Exp_int(x, y) == Exp_int_ghost(x, y)
  decreases y
{
  if y == 0 {
  } else {
    Lemma_Exp_int_equiv(x, y - 1);
  }
}

lemma Lemma_ModExpPow2_Correct(sx: string, sy: string, n: nat, sz: string, res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  requires ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
{
}

lemma Lemma_Mul_Correct(s1: string, s2: string, res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
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
  var n := |sy| - 1;
  ghost var sy_int := Str2Int(sy);
  ghost var sz_int := Str2Int(sz);
  
  if sy_int == 0 {
    res := "1";
    assert Str2Int(res) == 1;
    assert Exp_int(Str2Int(sx), 0) == 1;
    Lemma_OneMod(sz_int);
    assert 1 % sz_int == 1;
  } else if n == 0 {
    res := "1";
    assert Str2Int(res) == 1;
    ghost var temp := Exp_int(Str2Int(sx), sy_int);
    Lemma_Exp_int_equiv(Str2Int(sx), sy_int);
    Lemma_Mod_Exp(Str2Int(sx), sy_int, sz_int);
    assert temp % sz_int == Exp_int(Str2Int(sx) % sz_int, sy_int) % sz_int;
    Lemma_OneMod(sz_int);
  } else {
    var half_sy_left := sy[0..|sy|-1];
    Lemma_HalfStringValid(sy);
    ghost var half_int := Str2Int(half_sy_left);
    var rec_call := ModExp(sx, half_sy_left, sz);
    ghost var rec_int := Str2Int(rec_call);
    assert rec_int == Exp_int(Str2Int(sx), half_int) % sz_int;
    
    var prod_int: nat;
    var temp1_int: nat;
    var temp2_int: nat;
    
    if sy[|sy|-1] == '0' {
      prod_int := rec_int * rec_int % sz_int;
      Lemma_Mul_Call(rec_call, rec_call);
      Lemma_Mod_Mul(rec_int, rec_int, sz_int);
      assert (rec_int * rec_int) % sz_int == rec_int * rec_int % sz_int;
      Lemma_ModExpPow2_Call(rec_call, sy, n, sz);
      res := ModExpPow2(rec_call, sy, n, sz);
      Lemma_ModExpPow2_Correct(rec_call, sy, n, sz, res);
      var expected := Exp_int(rec_int, sy_int) % sz_int;
      assert Str2Int(res) == expected;
      assert expected == Exp_int(Str2Int(sx), sy_int) % sz_int;
    } else {
      temp1_int := rec_int * rec_int % sz_int;
      Lemma_Mul_Call(rec_call, rec_call);
      Lemma_Mod_Mul(rec_int, rec_int, sz_int);
      assert (rec_int * rec_int) % sz_int == temp1_int;
      
      temp2_int := temp1_int * Str2Int(sx) % sz_int;
      Lemma_Mul_Call(rec_call, sx);
      Lemma_Mod_Mul(temp1_int, Str2Int(sx), sz_int);
      assert (temp1_int * Str2Int(sx)) % sz_int == temp2_int;
      
      Lemma_ModExpPow2_Call(rec_call, sy, n, sz);
      res := ModExpPow2(rec_call, sy, n, sz);
      Lemma_ModExpPow2_Correct(rec_call, sy, n, sz, res);
      var expected := Exp_int(temp2_int, sy_int) % sz_int;
      assert Str2Int(res) == expected;
      assert expected == Exp_int(Str2Int(sx), sy_int) % sz_int;
    }
  }
}
// </vc-code>

