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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ModExpProperty(a: nat, b: nat, n: nat)
  requires n > 0
  ensures (a * b) % n == ((a % n) * (b % n)) % n
{
}

lemma ExpIntProperty(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma ExpIntEven(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    assert Exp_int(x, 2) == x * x;
    assert Exp_int(x * x, 1) == x * x;
  } else {
    var half := y / 2;
    assert y == 2 * half;
    ExpIntEven(x, half);
  }
}

lemma ExpIntOdd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
{
  if y == 1 {
    assert Exp_int(x, 1) == x;
    assert Exp_int(x * x, 0) == 1;
  } else {
    var half := y / 2;
    assert y == 2 * half + 1;
    ExpIntEven(x, half);
  }
}

method MultMod(a: string, b: string, n: string) returns (res: string)
  requires ValidBitString(a) && ValidBitString(b) && ValidBitString(n)
  requires Str2Int(n) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(a) * Str2Int(b)) % Str2Int(n)
{
  var prod := IntToStr(Str2Int(a) * Str2Int(b));
  var _, rem := DivMod(prod, n);
  res := rem;
}

method IntToStr(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  if n == 0 {
    s := "0";
  } else {
    var q := n / 2;
    var r := n % 2;
    var qs := IntToStr(q);
    if r == 0 {
      s := qs + "0";
    } else {
      s := qs + "1";
    }
  }
}

method IsZero(s: string) returns (b: bool)
  requires ValidBitString(s)
  ensures b == (Str2Int(s) == 0)
{
  b := true;
  for i := 0 to |s|
    invariant b == (forall j :: 0 <= j < i ==> s[j] == '0')
  {
    if s[i] != '0' {
      b := false;
    }
  }
}

method IsOne(s: string) returns (b: bool)
  requires ValidBitString(s)
  ensures b == (Str2Int(s) == 1)
{
  if |s| == 0 {
    b := false;
  } else if |s| == 1 {
    b := s[0] == '1';
  } else {
    b := s[|s|-1] == '1';
    for i := 0 to |s| - 1
      invariant b == (s[|s|-1] == '1' && forall j :: 0 <= j < i ==> s[j] == '0')
    {
      if s[i] != '0' {
        b := false;
      }
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
  var isZero := IsZero(sy);
  if isZero {
    res := "1";
    return;
  }
  
  var isOne := IsOne(sy);
  if isOne {
    var _, rem := DivMod(sx, sz);
    res := rem;
    return;
  }
  
  var two := "10";
  var q, r := DivMod(sy, two);
  var recRes := ModExp(sx, q, sz);
  var squared := MultMod(recRes, recRes, sz);
  
  var isRZero := IsZero(r);
  if isRZero {
    res := squared;
  } else {
    var _, xMod := DivMod(sx, sz);
    res := MultMod(xMod, squared, sz);
  }
}
// </vc-code>

