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

lemma Str2IntConcat(s: string, c: char)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures ValidBitString(s + [c])
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  var divInt := Str2Int(dividend);
  var divisorInt := Str2Int(divisor);
  var q := divInt / divisorInt;
  var r := divInt % divisorInt;
  quotient := IntToStr(q);
  remainder := IntToStr(r);
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
    s := "";
    var m := n;
    while m > 0
      invariant 0 <= m <= n
      invariant ValidBitString(s)
      invariant Str2Int(s) * Exp_int(2, BitCount(m)) + m == n
      decreases m
    {
      var bit := if m % 2 == 1 then '1' else '0';
      s := s + [bit];
      m := m / 2;
    }
  }
}

function BitCount(n: nat): nat
{
  if n == 0 then 0 else 1 + BitCount(n / 2)
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
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    return;
  }
  
  var isOne := IsOne(sy);
  if isOne {
    var _, rem := DivMod(sx, sz);
    res := rem;
    assert Str2Int(sy) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    return;
  }
  
  var two := "10";
  var q, r := DivMod(sy, two);
  var recRes := ModExp(sx, q, sz);
  var squared := MultMod(recRes, recRes, sz);
  
  var isRZero := IsZero(r);
  if isRZero {
    res := squared;
    ExpIntEven(Str2Int(sx), Str2Int(sy));
  } else {
    var _, xMod := DivMod(sx, sz);
    res := MultMod(xMod, squared, sz);
    ExpIntOdd(Str2Int(sx), Str2Int(sy));
    ModExpProperty(Str2Int(sx), Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2), Str2Int(sz));
  }
}
// </vc-code>

