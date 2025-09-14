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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Lemma_Exp_mod(x: nat, y: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, y) % m == (if y == 0 then 1 % m else (x * (Exp_int(x, y - 1) % m)) % m)
  decreases y
{
  if y != 0 {
    Lemma_Exp_mod(x, y - 1, m);
    calc {
      Exp_int(x, y) % m;
      == 
      (x * Exp_int(x, y - 1)) % m;
      == 
      { Lemma_MulMod(x, Exp_int(x, y - 1), m); }
      (x % m) * (Exp_int(x, y - 1) % m) % m;
      == 
      { if x % m == x {} }
      x * (Exp_int(x, y - 1) % m) % m;
    }
  } else {
  }
}

lemma Lemma_MulMod(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == (a % m) * (b % m) % m
{
  calc {
    (a * b) % m;
    == 
    ((a % m) + (a / m) * m) * ((b % m) + (b / m) * m) % m;
    == 
    ((a % m) * (b % m) + (a % m) * (b / m) * m + (a / m) * m * (b % m) + (a / m) * (b / m) * m * m) % m;
    == 
    (a % m) * (b % m) % m;
  }
}

lemma Lemma_Exp_mod_addition(x: nat, a: nat, b: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, a + b) % m == (Exp_int(x, a) * Exp_int(x, b)) % m
  decreases a
{
  if a == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, b) == 1 * Exp_int(x, b);
  } else {
    Lemma_Exp_mod_addition(x, a - 1, b, m);
    calc {
      Exp_int(x, a + b) % m;
      ==
      (x * Exp_int(x, a - 1 + b)) % m;
      ==
      { Lemma_MulMod(x, Exp_int(x, a - 1 + b), m); }
      (x % m) * (Exp_int(x, a - 1 + b) % m) % m;
      ==
      (x % m) * ((Exp_int(x, a - 1) * Exp_int(x, b)) % m) % m;
      ==
      { Lemma_MulMod(x % m, (Exp_int(x, a - 1) * Exp_int(x, b)) % m, m); }
      (x % m) * (Exp_int(x, a - 1) * Exp_int(x, b)) % m % m;
      ==
      (x * Exp_int(x, a - 1) * Exp_int(x, b)) % m;
      ==
      (Exp_int(x, a) * Exp_int(x, b)) % m;
    }
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
    var n := |sy| - 1;
    res := ModExpPow2(sx, sy, n, sz);
  } else {
    var s_y_half := sy[0..|sy|-1];
    assert ValidBitString(s_y_half);
    var mod_res1 := ModExp(sx, s_y_half, sz);
    var squared := Mul(mod_res1, mod_res1);
    var mod_res2 := ModExpPow2(squared, "10", 1, sz);
    
    if sy[|sy|-1] == '0' {
      res := mod_res2;
    } else {
      var multiplied := Mul(mod_res2, sx);
      var mod_res3 := ModExpPow2(multiplied, "10", 1, sz);
      res := mod_res3;
    }
  }
}
// </vc-code>

