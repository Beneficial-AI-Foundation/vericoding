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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Exp_step(x: nat, i: nat)
  ensures x * Exp_int(x, i) == Exp_int(x, i + 1)
{
  assert i + 1 > 0;
  assert Exp_int(x, i + 1) == x * Exp_int(x, (i + 1) - 1);
  assert (i + 1) - 1 == i;
  calc {
    x * Exp_int(x, i);
    == { }
    x * Exp_int(x, (i + 1) - 1);
    == { }
    Exp_int(x, i + 1);
  }
}

function Str2IntM(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * Str2IntM(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma Str2IntM_eq(s: string)
  requires ValidBitString(s)
  ensures Str2IntM(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
  } else {
    Str2IntM_eq(s[0..|s|-1]);
    calc {
      Str2IntM(s);
      == { }
      2 * Str2IntM(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { }
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { }
      Str2Int(s);
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
  var y: nat := Str2IntM(sy);
  Str2IntM_eq(sy);
  assert y == Str2Int(sy);

  var acc: string := "1";
  var i: nat := 0;
  while i < y
    invariant ValidBitString(acc)
    invariant Str2Int(acc) == Exp_int(Str2Int(sx), i)
    invariant i <= y
    decreases y - i
  {
    var prod := Mul(sx, acc);
    calc {
      Str2Int(prod);
      == { assert Str2Int(prod) == Str2Int(sx) * Str2Int(acc); }
      Str2Int(sx) * Str2Int(acc);
      == { assert Str2Int(acc) == Exp_int(Str2Int(sx), i); }
      Str2Int(sx) * Exp_int(Str2Int(sx), i);
      == { Exp_step(Str2Int(sx), i); }
      Exp_int(Str2Int(sx), i + 1);
    }
    acc := prod;
    i := i + 1;
  }
  assert i == y;
  assert Str2Int(acc) == Exp_int(Str2Int(sx), y);

  var quotient, remainder := DivMod(acc, sz);
  res := remainder;

  calc {
    Str2Int(res);
    == { }
    Str2Int(remainder);
    == { }
    Str2Int(acc) % Str2Int(sz);
    == { assert Str2Int(acc) == Exp_int(Str2Int(sx), y); }
    Exp_int(Str2Int(sx), y) % Str2Int(sz);
    == { assert y == Str2Int(sy); }
    Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  }
}
// </vc-code>

