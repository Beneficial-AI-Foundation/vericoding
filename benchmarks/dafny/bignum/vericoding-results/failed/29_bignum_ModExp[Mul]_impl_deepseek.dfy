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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpModLemma(a: nat, b: nat, m: nat)
  requires m > 1
  ensures Exp_int(a, b) % m == (if b == 0 then 1 % m else (a * (Exp_int(a, b - 1) % m)) % m)
{
  if b > 0 {
    calc {
      Exp_int(a, b) % m;
      (a * Exp_int(a, b - 1)) % m;
      { ModMultDistr(a, Exp_int(a, b - 1), m); }
      (a * (Exp_int(a, b - 1) % m)) % m;
    }
  }
}

lemma ModMultDistr(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == (a * (b % m)) % m
{
  calc {
    (a * b) % m;
    (a * (b % m)) % m;
  }
}

lemma ExpIntZero(x: nat, y: nat)
  ensures Exp_int(x, 0) == 1
{
}

ghost function ModExpHelper(x: nat, y: nat, m: nat): nat
  requires m > 1
  ensures ModExpHelper(x, y, m) == Exp_int(x, y) % m
  decreases y
{
  if y == 0 then
    1 % m
  else
    (x * ModExpHelper(x, y - 1, m)) % m
}

function NatToBitString(n: nat): string
  decreases n
{
  if n == 0 then "0" else 
  if n == 1 then "1" else 
  NatToBitString(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma NatToBitStringValid(n: nat)
  ensures ValidBitString(NatToBitString(n))
  decreases n
{
  if n > 1 {
    NatToBitStringValid(n / 2);
  }
}

lemma NatToBitStringCorrect(n: nat)
  ensures Str2Int(NatToBitString(n)) == n
  decreases n
{
  if n > 1 {
    NatToBitStringCorrect(n / 2);
  }
}

lemma ModExpHelperLemma(x: nat, y: nat, m: nat)
  requires m > 1
  ensures ModExpHelper(x, y, m) == Exp_int(x, y) % m
{
}

lemma SplitPowerLemma(x: nat, hi: nat, lo: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, hi * 2 + lo) % m == ((Exp_int(x, hi) % m) * (Exp_int(x, hi) % m) * (Exp_int(x, lo) % m)) % m
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
  ghost var x_val := Str2Int(sx);
  ghost var y_val := Str2Int(sy);
  ghost var z_val := Str2Int(sz);
  
  var result_val: nat;
  
  if y_val == 0 {
    result_val := 1 % z_val;
    ghost var ghost_val := result_val;
  } else {
    var half_len := |sy| / 2;
    var y_hi := sy[0..half_len];
    var y_lo := sy[half_len..|sy|];
    ghost var lo_val := Str2Int(y_lo);
    ghost var hi_val := Str2Int(y_hi);
    
    ghost var hi_res_val := ModExpHelper(x_val, hi_val, z_val);
    ghost var pow_res_val := ModExpHelper(hi_res_val, 2, z_val);
    
    if lo_val == 0 {
      result_val := pow_res_val;
      ghost var ghost_val := result_val;
    } else {
      ghost var lo_res_val := ModExpHelper(x_val, lo_val, z_val);
      result_val := (pow_res_val * lo_res_val) % z_val;
      ghost var ghost_val := result_val;
    }
  }
  res := NatToBitString(result_val);
}
// </vc-code>

