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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
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
lemma Str2Int_NonEmpty(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1]=='1' then 1 else 0)
{
  if |s| == 0 {
    // Not possible due to precondition
  } else {
    calc {
      Str2Int(s);
      ==  { reveal Str2Int(); }
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1]=='1' then 1 else 0);
    }
  }
}

lemma ModExp_RecursionLemma(sx: string, sy: string, sz: string, y_prefix: string, last_char: char)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires |sy| > 1
  requires y_prefix == sy[0..|sy|-1]
  requires last_char == sy[|sy|-1]
  requires Str2Int(sz) > 1
  ensures var y := Str2Int(sy);
          var y' := Str2Int(y_prefix);
          var last_bit := if last_char == '1' then 1 else 0;
          y == 2 * y' + last_bit
{
  Str2Int_NonEmpty(sy);
  calc {
    Str2Int(sy);
    == { Str2Int_NonEmpty(sy); }
    2 * Str2Int(sy[0..|sy|-1]) + (if sy[|sy|-1]=='1' then 1 else 0);
    == { assert sy[0..|sy|-1] == y_prefix; assert sy[|sy|-1] == last_char; }
    2 * Str2Int(y_prefix) + (if last_char=='1' then 1 else 0);
  }
}

lemma Exp_int_Properties(x: nat, y: nat)
  ensures Exp_int(x, 2 * y) == Exp_int(Exp_int(x, y), 2)
  ensures y > 0 ==> Exp_int(x, 2 * y + 1) == Exp_int(Exp_int(x, y), 2) * x
{
  if y == 0 {
    calc {
      Exp_int(x, 2 * y);
      == { y == 0; }
      Exp_int(x, 0);
      == { reveal Exp_int(); }
      1;
      == { reveal Exp_int(); }
      Exp_int(1, 2);
      == { reveal Exp_int(); }
      Exp_int(Exp_int(x, y), 2);
    }
    calc {
      Exp_int(x, 2 * y + 1);
      == { y == 0; }
      Exp_int(x, 1);
      == { reveal Exp_int(); }
      x;
      == { x == 1 * x; }
      Exp_int(Exp_int(x, y), 2) * x;
    }
  } else {
    calc {
      Exp_int(x, 2 * y);
      == { reveal Exp_int(); }
      Exp_int(x, y + y);
      == { reveal Exp_int(); }
      x * Exp_int(x, y + y - 1);
      == { reveal Exp_int(); }
      x * (x * Exp_int(x, y + y - 2));
      == { reveal Exp_int(); }
      Exp_int(x, 2) * Exp_int(x, y + y - 2);
      == { reveal Exp_int(); }
      Exp_int(x, 2) * Exp_int(Exp_int(x, y - 1), 2);
    }
    calc {
      Exp_int(x, 2 * y + 1);
      == { reveal Exp_int(); }
      x * Exp_int(x, 2 * y);
      == { Exp_int(x, 2 * y) == Exp_int(Exp_int(x, y), 2); }
      x * Exp_int(Exp_int(x, y), 2);
    }
  }
}

lemma ModExp_OddCaseProperty(sx: string, sz: string, t_sq_mod: string, res: string)
  requires ValidBitString(sx) && ValidBitString(sz) && ValidBitString(t_sq_mod) && ValidBitString(res)
  requires Str2Int(sz) > 1
  requires Str2Int(res) == (Str2Int(t_sq_mod) * Str2Int(sx)) % Str2Int(sz)
  ensures Str2Int(res) == (Str2Int(t_sq_mod) * Str2Int(sx)) % Str2Int(sz)
{
  // The postcondition is identical to a precondition, making the lemma trivial.
  // This lemma is used to carry the property to the verification condition.
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
    if sy == "0" {
      res := "1";
    } else {
      // sy == "1", so we need sx % sz
      _ quotient, res := DivMod(sx, sz);
    }
  } else {
    var y_prefix := sy[0..|sy|-1];
    var last_char := sy[|sy|-1];
    
    ModExp_RecursionLemma(sx, sy, sz, y_prefix, last_char);
    var t_res := ModExp(sx, y_prefix, sz);
    var t_sq := Mul(t_res, t_res);
    var _ quotient2, t_sq_mod := DivMod(t_sq, sz);

    if last_char == '0' {
      res := t_sq_mod;
    } else {
      var t_mul := Mul(t_sq_mod, sx);
      var _ quotient3, t_res_divmod := DivMod(t_mul, sz);
      res := t_res_divmod;
      ModExp_OddCaseProperty(sx, sz, t_sq_mod, res);
    }
  }
}
// </vc-code>

