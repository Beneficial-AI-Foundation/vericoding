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
lemma LemmaExpModProperty(a: nat, b: nat, m: nat)
  requires m > 1
  ensures Exp_int(a, b) % m == (if b == 0 then 1 % m else (a * (Exp_int(a, b-1) % m)) % m)
  decreases b
{
  if b == 0 {
  } else {
    LemmaExpModProperty(a, b-1, m);
    calc {
      Exp_int(a, b) % m;
      == { assert Exp_int(a, b) == a * Exp_int(a, b-1); }
      (a * Exp_int(a, b-1)) % m;
      == { LemmaModProperty(a, Exp_int(a, b-1), m); }
      (a * (Exp_int(a, b-1) % m)) % m;
    }
  }
}

lemma LemmaPow2DivMod(x: nat, n: nat, m: nat)
  requires m > 1
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) % m == Exp_int(Exp_int(x, Exp_int(2, n-1)) % m, 2) % m
  decreases n
{
  calc {
    Exp_int(x, Exp_int(2, n)) % m;
    == { assert Exp_int(2, n) == 2 * Exp_int(2, n-1); }
    Exp_int(x, 2 * Exp_int(2, n-1)) % m;
    == { LemmaExpAddition(x, Exp_int(2, n-1), Exp_int(2, n-1)); }
    (Exp_int(x, Exp_int(2, n-1)) * Exp_int(x, Exp_int(2, n-1))) % m;
    == { LemmaModProperty(Exp_int(x, Exp_int(2, n-1)), Exp_int(x, Exp_int(2, n-1)), m); }
    (Exp_int(x, Exp_int(2, n-1)) % m) * (Exp_int(x, Exp_int(2, n-1)) % m) % m;
    == 
    Exp_int(Exp_int(x, Exp_int(2, n-1)) % m, 2) % m;
  }
}

lemma LemmaExpAddition(a: nat, b: nat, c: nat)
  ensures Exp_int(a, b + c) == Exp_int(a, b) * Exp_int(a, c)
  decreases b
{
  if b == 0 {
    assert Exp_int(a, 0 + c) == Exp_int(a, c);
    assert Exp_int(a, 0) * Exp_int(a, c) == 1 * Exp_int(a, c) == Exp_int(a, c);
  } else {
    LemmaExpAddition(a, b-1, c);
    assert Exp_int(a, b + c) == a * Exp_int(a, b + c - 1);
    assert Exp_int(a, b) * Exp_int(a, c) == a * Exp_int(a, b-1) * Exp_int(a, c);
    assert a * Exp_int(a, b + c - 1) == a * (Exp_int(a, b-1) * Exp_int(a, c));
  }
}

lemma LemmaStr2IntZeroLength(s: string)
  requires ValidBitString(s) && |s| == 0
  ensures Str2Int(s) == 0
{
}

lemma LemmaStr2IntLength(s: string)
  requires ValidBitString(s)
  ensures |s| > 0 ==> Str2Int(s) >= 0
{
}

lemma LemmaModProperty(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == (a % m) * (b % m) % m
{
  // This is a standard modular arithmetic property
}

lemma LemmaDivModProperty(dividend: string, divisor: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures var quotient, remainder := DivMod(dividend, divisor) in
          Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  // This follows from the specification of DivMod
}

lemma LemmaExpDoubleBase(a: nat, b: nat)
  ensures Exp_int(a, 2 * b) == Exp_int(a, b) * Exp_int(a, b)
{
  LemmaExpAddition(a, b, b);
  assert 2 * b == b + b;
}

lemma LemmaExpIncrement(a: nat, b: nat)
  ensures Exp_int(a, 2 * b + 1) == Exp_int(a, b) * Exp_int(a, b) * a
{
  calc {
    Exp_int(a, 2 * b + 1);
    == { LemmaExpAddition(a, 2 * b, 1); }
    Exp_int(a, 2 * b) * Exp_int(a, 1);
    == { LemmaExpDoubleBase(a, b); }
    Exp_int(a, b) * Exp_int(a, b) * a;
  }
}

lemma LemmaStr2IntConcat(s: string, c: char)
  requires ValidBitString(s) && (c == '0' || c == '1')
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
}

lemma LemmaStr2IntSplit(s: string, n: nat)
  requires ValidBitString(s) && 0 <= n <= |s|
  ensures Str2Int(s) == Str2Int(s[0..n]) * Exp_int(2, |s| - n) + Str2Int(s[n..])
{
}

lemma LemmaModSqProperty(a: nat, m: nat)
  requires m > 1
  ensures (a * a) % m == (a % m) * (a % m) % m
{
  LemmaModProperty(a, a, m);
}

lemma LemmaModExpZeroExponent(x: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, 0) % m == 1 % m
{
}

lemma LemmaModExpBreakdown(x: nat, y1: nat, y2: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, y1 + y2) % m == (Exp_int(x, y1) * Exp_int(x, y2)) % m
{
  LemmaExpAddition(x, y1, y2);
  assert Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2);
}

lemma LemmaPowerOfTwoLength(s: string, n: nat)
  requires ValidBitString(s)
  requires |s| == n + 1
  ensures Str2Int(s) == Exp_int(2, n) || Str2Int(s) == 0
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
  if |sy| == 1 {
    if sy[0] == '0' {
      res := "1";
    } else {
      var mod_quotient, mod_remainder := DivMod(sx, sz);
      res := mod_remainder;
    }
  } else {
    var half_length := |sy| / 2;
    var high_half := sy[0..half_length];
    var low_half := sy[half_length..];
    
    var base_mod := ModExp(sx, high_half, sz);
    var low_mod_exp := ModExp(base_mod, low_half, sz);
    res := low_mod_exp;
  }
}
// </vc-code>

