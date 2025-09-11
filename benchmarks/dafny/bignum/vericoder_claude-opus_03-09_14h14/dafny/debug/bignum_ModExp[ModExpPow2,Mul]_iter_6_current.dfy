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
lemma ExpRecursive(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma ExpZero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma ExpOne(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma Str2IntBitShift(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
}

lemma ModMulProperty(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma ModExpProperty(a: nat, b: nat, m: nat)
  requires m > 1
  ensures Exp_int(a, b) % m == Exp_int(a % m, b) % m
  decreases b
{
  if b == 0 {
    // Base case: Exp_int(a, 0) == 1 == Exp_int(a % m, 0)
  } else {
    // Inductive case - simplified
    ModExpProperty(a, b - 1, m);
    ModMulProperty(a, Exp_int(a, b - 1), m);
    ModMulProperty(a % m, Exp_int(a % m, b - 1), m);
  }
}

lemma ExpDoubling(x: nat, n: nat)
  ensures Exp_int(x, 2 * n) == Exp_int(x * x, n)
  decreases n
{
  if n == 0 {
    // Base case
  } else {
    ExpDoubling(x, n - 1);
  }
}

lemma ExpAddition(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases a
{
  if a == 0 {
    // Base case
  } else {
    ExpAddition(x, a - 1, b);
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
    if sy[0] == '0' {
      res := "1";
      ExpZero(Str2Int(sx));
    } else {
      ExpOne(Str2Int(sx));
      var temp := Mul(sx, "1");
      res := ModExpPow2(temp, "1", 0, sz);
    }
  } else {
    var sy_prefix := sy[0..|sy|-1];
    Str2IntBitShift(sy);
    
    var rec_result := ModExp(sx, sy_prefix, sz);
    
    if sy[|sy|-1] == '0' {
      var squared := Mul(rec_result, rec_result);
      res := ModExpPow2(squared, "1", 0, sz);
      
      assert Str2Int(sy) == 2 * Str2Int(sy_prefix);
      assert Str2Int(rec_result) == Exp_int(Str2Int(sx), Str2Int(sy_prefix)) % Str2Int(sz);
      
      // Simplified proof
      ExpDoubling(Str2Int(sx), Str2Int(sy_prefix));
      ModMulProperty(Exp_int(Str2Int(sx), Str2Int(sy_prefix)), 
                     Exp_int(Str2Int(sx), Str2Int(sy_prefix)), 
                     Str2Int(sz));
    } else {
      var squared := Mul(rec_result, rec_result);
      var squared_mod := ModExpPow2(squared, "1", 0, sz);
      var product := Mul(squared_mod, sx);
      res := ModExpPow2(product, "1", 0, sz);
      
      assert Str2Int(sy) == 2 * Str2Int(sy_prefix) + 1;
      assert Str2Int(rec_result) == Exp_int(Str2Int(sx), Str2Int(sy_prefix)) % Str2Int(sz);
      
      // Simplified proof
      ExpDoubling(Str2Int(sx), Str2Int(sy_prefix));
      ExpRecursive(Str2Int(sx), 2 * Str2Int(sy_prefix) + 1);
      ModMulProperty(Exp_int(Str2Int(sx), 2 * Str2Int(sy_prefix)), 
                     Str2Int(sx), 
                     Str2Int(sz));
    }
  }
}
// </vc-code>

