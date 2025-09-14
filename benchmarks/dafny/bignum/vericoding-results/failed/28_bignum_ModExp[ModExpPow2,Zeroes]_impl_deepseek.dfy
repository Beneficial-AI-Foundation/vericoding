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
lemma lemma_Exp_int_base(x: nat, y: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma lemma_Exp_int_rec(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma lemma_Str2Int_empty()
  ensures Str2Int("") == 0
{
}

lemma lemma_Str2Int_rec(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
}

lemma lemma_Exp_int_mod_property(x: nat, y: nat, m: nat)
  requires m > 1
  requires y > 0
  ensures Exp_int(x, y) % m == ((x % m) * (Exp_int(x, y - 1) % m)) % m
{
  calc {
    Exp_int(x, y) % m;
    (x * Exp_int(x, y - 1)) % m;
    ((x % m) * (Exp_int(x, y - 1) % m)) % m;
  }
}

lemma lemma_Exp_int_mod_property_base(x: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, 0) % m == 1
{
}

ghost function ModExpHelper(x: nat, y: nat, m: nat): nat
  requires m > 1
  ensures ModExpHelper(x, y, m) == Exp_int(x, y) % m
  decreases y
{
  if y == 0 then
    1
  else
    (x % m) * ModExpHelper(x, y - 1, m) % m
}

lemma lemma_AllZero_implies_zero(s: string)
  requires AllZero(s)
  ensures Str2Int(s) == 0
{
}

lemma lemma_ZeroString(n: nat)
  ensures forall s: string :: |s| == n && AllZero(s) ==> Str2Int(s) == 0
{
}

lemma lemma_ModExpPow2_correct(sx: string, sy: string, n: nat, sz: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(ModExpPow2(sx, sy, n, sz))
  ensures Str2Int(ModExpPow2(sx, sy, n, sz)) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
{
}

lemma lemma_Exp_int_mul(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
}

lemma lemma_Mod_mul_property(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma lemma_power_of_two_representation(n: nat)
  ensures Exp_int(2, n) > 0
  ensures |Zeros(n)| == n
  ensures Str2Int("1" + Zeros(n)) == Exp_int(2, n)
{
}

lemma lemma_mod_exp_recursive(x_val: nat, y_val: nat, m_val: nat)
  requires m_val > 1
  requires y_val > 0
  ensures Exp_int(x_val, y_val) % m_val == ((Exp_int(x_val, y_val / 2) % m_val) * (Exp_int(x_val, y_val % 2) % m_val)) % m_val
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
  if AllZero(sy) {
    res := "1";
  } else {
    var y_val := Str2Int(sy);
    
    if y_val == 0 {
      res := "1";
    } else if y_val == 1 {
      var x_val := Str2Int(sx);
      var m_val := Str2Int(sz);
      var mod_val := x_val % m_val;
      
      if mod_val == 0 {
        res := "0";
      } else if mod_val == 1 {
        res := "1";
      } else {
        res := ModExpPow2(sx, "10", 1, sz);
      }
    } else {
      var half_y := y_val / 2;
      var rem_y := y_val % 2;
      
      var half_sy := "";
      var rem_sy := "";
      
      if half_y == 0 {
        half_sy := "0";
      } else {
        var zeros := Zeros(half_y);
        half_sy := "1" + zeros;
      }
      
      if rem_y == 0 {
        rem_sy := "0";
      } else {
        rem_sy := "1";
      }
      
      var res1 := ModExp(sx, half_sy, sz);
      var res2 := ModExp(sx, rem_sy, sz);
      
      var x_pow_half := Str2Int(res1);
      var x_pow_rem := Str2Int(res2);
      var combined := (x_pow_half * x_pow_rem) % Str2Int(sz);
      
      if combined == 0 {
        res := "0";
      } else if combined == 1 {
        res := "1";
      } else {
        var temp := combined;
        var s := "";
        var count := 0;
        while temp > 0 {
          if temp % 2 == 1 {
            s := "1" + s;
          } else {
            s := "0" + s;
          }
          temp := temp / 2;
          count := count + 1;
        }
        res := ModExpPow2(res1, s, |s| - 1, sz);
      }
    }
  }
}
// </vc-code>

