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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma DivMod2(n: nat)
  ensures n == 2*(n/2) + n%2
  decreases n
{
  if n == 0 {
  } else {
    DivMod2(n/2);
    assert n == 2*(n/2) + n%2;
  }
}

method Str2Int_exec(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    n := 0;
  } else {
    var pref := Str2Int_exec(s[0..|s|-1]);
    if s[|s|-1] == '1' {
      n := 2 * pref + 1;
    } else {
      n := 2 * pref;
    }
  }
}

method Exp_int_exec(x: nat, y: nat) returns (r: nat)
  ensures r == Exp_int(x, y)
  decreases y
{
  if y == 0 {
    r := 1;
  } else {
    var t := Exp_int_exec(x, y - 1);
    r := x * t;
  }
}

method Nat2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "";
    assert ValidBitString(s);
    assert Str2Int(s) == 0;
  } else {
    var pref := Nat2Str(n / 2);
    var bit := if n % 2 == 1 then "1" else "0";
    s := pref + bit;
    // From recursive call
    assert Str2Int(pref) == n / 2;
    // By definition of Str2Int for non-empty s:
    assert Str2Int(s) == 2 * Str2Int(pref) + (if n % 2 == 1 then 1 else 0);
    DivMod2(n);
    assert Str2Int(s) == n;
    assert ValidBitString(s);
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
  var nsx := Str2Int_exec(sx);
  var nsy := Str2Int_exec(sy);
  var nsz := Str2Int_exec(sz);
  var numExp := Exp_int_exec(nsx, nsy);
  var num := numExp % nsz;
  res := Nat2Str(num);
}
// </vc-code>

