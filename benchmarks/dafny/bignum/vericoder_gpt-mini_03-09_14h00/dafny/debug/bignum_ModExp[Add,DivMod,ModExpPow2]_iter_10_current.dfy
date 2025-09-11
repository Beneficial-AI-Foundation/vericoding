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
lemma Exp_int_succ(x: nat, y: nat)
  ensures Exp_int(x, y+1) == Exp_int(x, y) * x
  decreases y
{
  if y == 0 {
    // By definition of Exp_int: Exp_int(x,1) = x * Exp_int(x,0) and Exp_int(x,0) = 1
    assert Exp_int(x, 1) == (if 1 == 0 then 1 else x * Exp_int(x, 0));
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, 1) == Exp_int(x, 0) * x;
  } else {
    // By definition of Exp_int for y+1 > 0
    assert Exp_int(x, y+1) == (if y+1 == 0 then 1 else x * Exp_int(x, y));
    assert Exp_int(x, y+1) == x * Exp_int(x, y);
    assert Exp_int(x, y) * x == Exp_int(x, y) * x;
  }
}

function method Str2Nat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * Str2Nat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function method Nat2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Nat2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Str2Nat_equiv(s: string)
  requires ValidBitString(s)
  ensures Str2Nat(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
  } else {
    Str2Nat_equiv(s[0..|s|-1]);
    assert Str2Nat(s) == 2 * Str2Nat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Nat(s[0..|s|-1]) == Str2Int(s[0..|s|-1]);
    calc {
      Str2Nat(s);
      == { }
      2 * Str2Nat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { assert Str2Nat(s[0..|s|-1]) == Str2Int(s[0..|s|-1]); }
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == { }
      Str2Int(s);
    }
  }
}

lemma Nat2Str_equiv(n: nat)
  ensures Str2Nat(Nat2Str(n)) == n
  decreases n
{
  if n == 0 {
  } else {
    Nat2Str_equiv(n / 2);
    assert Str2Nat(Nat2Str(n)) == 2 * Str2Nat(Nat2Str(n / 2)) + (if Nat2Str(n)[|Nat2Str(n)| - 1] == '1' then 1 else 0);
    // By definition of Nat2Str, the last character corresponds to n % 2
    assert (if Nat2Str(n)[|Nat2Str(n)| - 1] == '1' then 1 else 0) == (if n % 2 == 1 then 1 else 0);
    assert Str2Nat(Nat2Str(n / 2)) == (n / 2);
    calc {
      Str2Nat(Nat2Str(n));
      == { }
      2 * Str2Nat(Nat2Str(n / 2)) + (if n % 2 == 1 then 1 else 0);
      == { assert Str2Nat(Nat2Str(n / 2)) == n / 2; }
      2 * (n / 2) + (if n % 2 == 1 then 1 else 0);
      == { }
      n;
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
  var base := Str2Nat(sx);
  var exp := Str2Nat(sy);
  var m := Str2Nat(sz);
  var p := 1;
  var i := 0;
  while i < exp
    invariant 0 <= i <= exp
    invariant p == Exp_int(base, i)
    decreases exp - i
  {
    Exp_int_succ(base, i);
    p := p * base;
    i := i + 1;
  }
  var r := p % m;
  res := Nat2Str(r);
}
// </vc-code>

