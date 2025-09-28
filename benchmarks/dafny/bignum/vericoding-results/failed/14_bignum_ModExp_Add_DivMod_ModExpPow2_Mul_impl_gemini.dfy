// <vc-preamble>
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

  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
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

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)

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
// </vc-preamble>

// <vc-helpers>
lemma ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  assert (a*b)%m == ((a%m)*b)%m;
  assert ((a%m)*b)%m == ((a%m)*(b%m))%m;
}

lemma ExpIntDouble(x: nat, a: nat)
  ensures Exp_int(x, 2 * a) == Exp_int(x, a) * Exp_int(x, a)
  decreases a
{
  if a == 0 {
  } else {
    calc {
      Exp_int(x, 2 * a);
      x * Exp_int(x, 2 * a - 1);
      x * x * Exp_int(x, 2 * a - 2);
      x * x * Exp_int(x, 2 * (a - 1));
      == { ExpIntDouble(x, a - 1); }
      x * x * (Exp_int(x, a - 1) * Exp_int(x, a - 1));
      (x * Exp_int(x, a - 1)) * (x * Exp_int(x, a - 1));
      Exp_int(x, a) * Exp_int(x, a);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)

  requires |sy| > 0 && Str2Int(sz) > 1
  decreases |sy|
// </vc-spec>
// <vc-code>
{
  if |sy| == 1 {
    if sy[0] == '0' {
      res := "1";
    } else {
      var _, rem := DivMod(sx, sz);
      res := rem;
    }
  } else {
    var sy_prefix := sy[0..|sy|-1];
    var temp_res := ModExp(sx, sy_prefix, sz);
    
    var temp_res_sq := Mul(temp_res, temp_res);
    var _, temp_res_sq_mod_z := DivMod(temp_res_sq, sz);

    if sy[|sy|-1] == '0' {
      res := temp_res_sq_mod_z;
    } else {
      var sx_mult_sq := Mul(sx, temp_res_sq_mod_z);
      var _, final_res := DivMod(sx_mult_sq, sz);
      res := final_res;
    }
  }
}
// </vc-code>
