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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function RepeatZero(k: nat): string
  decreases k
{
  if k == 0 then "" else "0" + RepeatZero(k-1)
}
function ShiftLeft(s: string, k: nat): string
{
  s + RepeatZero(k)
}
method AddHelper(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  res := "";
  var carry := 0;
  var i := 0;
  while i < |s1| || i < |s2| || carry > 0 
    invariant ValidBitString(res)
    invariant carry == 0 || carry == 1
    invariant Str2Int(res) == (carry as int) * Exp_int(2, i) + Str2Int(s1) % Exp_int(2, i) + Str2Int(s2) % Exp_int(2, i)
    decreases |s1| - i, |s2| - i, if carry > 0 then 1 else 0
  {
    var a : int := if i < |s1| then if s1[|s1|-1 - i] == '1' then 1 else 0 else 0;
    var b : int := if i < |s2| then if s2[|s2|-1 - i] == '1' then 1 else 0 else 0;
    var sum := a + b + carry;
    carry := sum / 2;
    res := (if sum % 2 == 1 then "1" else "0") + res;
    i := i + 1;
  }
}
method MulHelper(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  res := "0";
  var pos := 0;
  while pos < |s2|
    invariant ValidBitString(res)
    invariant Str2Int(res) == Str2Int(s1) * Str2Int(s2[|s2|-pos..]) % Exp_int(2, pos)
    decreases |s2| - pos
  {
    if s2[|s2|-1 - pos] == '1' {
      var shifted := ShiftLeft(s1, pos);
      res := AddHelper(res, shifted);
    }
    pos := pos + 1;
  }
}
method Int2Str(n: nat) returns (result: string)
  decreases n
  ensures ValidBitString(result)
  ensures Str2Int(result) == n
{
  if n == 0 {
    result := "0";
  } else {
    var high := Int2Str(n / 2);
    var low := if n % 2 == 1 then "1" else "0";
    result := high + low;
  }
}
method GtHelper(s1: string, s2: string, i: nat) returns (r: bool)
  requires ValidBitString(s1) && ValidBitString(s2) && |s1| == |s2| && i <= |s1|
  ensures r == (if i >= |s1| then false else if s1[i] > s2[i] then true else if s1[i] < s2[i] then false else GtHelper(s1, s2, i + 1))
  decreases |s1| - i
{
  if i >= |s1| {
    r := false;
  } else if s1[i] > s2[i] {
    r := true;
  } else if s1[i] < s2[i] {
    r := false;
  } else {
    r := GtHelper(s1, s2, i + 1);
  }
}
method Gt(s1: string, s2: string) returns (r: bool)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures r == (Str2Int(s1) > Str2Int(s2))
  decreases |s1| + |s2|
{
  if |s1| > |s2| {
    r := true;
  } else if |s1| < |s2| {
    r := false;
  } else {
    r := GtHelper(s1, s2, 0);
  }
}
method IsZero(s: string) returns (r: bool)
  requires ValidBitString(s)
  ensures r == (Str2Int(s) == 0)
  decreases |s|
{
  if |s| == 0 {
    r := true;
  } else if s[|s|-1] == '1' {
    r := false;
  } else {
    r := IsZero(s[0..|s|-1]);
  }
}
method SubHelper(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
  decreases |s1|
{
  res := "";
  var borrow := 0;
  var i := 0;
  while i < |s1| || borrow > 0
    invariant ValidBitString(res)
    invariant 0 <= borrow <= 1
    decreases |s1| - i
  {
    var a := if i < |s1| && s1[|s1|-1 - i] == '1' then 1 else 0;
    var b := if i < |s2| && s2[|s2|-1 - i] == '1' then 1 else 0;
    var diff := a - b - borrow;
    if diff < 0 {
      diff := diff + 2;
      borrow := 1;
    } else {
      borrow := 0;
    }
    var res_char := if diff == 1 then "1" else "0";
    res := res_char + res;
    i := i + 1;
  }
}
method ModHelper(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2) && Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)
  decreases Str2Int(s1)  // Ghost function in decreases is allowed for termination
{
  ghost var orig := Str2Int(s1);
  if Str2Int(s1) < Str2Int(s2) {
    res := s1;
  } else {
    res := s1;
    while Gt(res, s2)
      decreases Str2Int(res)
      invariant ValidBitString(res)
      invariant Str2Int(res) <= orig
      invariant Str2Int(res) >= Str2Int(s2) - 1
    {
      ghost var prev := Str2Int(res);
      res := SubHelper(res, s2);
      assert Str2Int(res) < prev;
    }
  }
}
method ModMul(a: string, b: string, m: string) returns (res: string)
  requires ValidBitString(a) && ValidBitString(b) && ValidBitString(m) && Str2Int(m) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(a) * Str2Int(b) % Str2Int(m)
{
  var product_str := MulHelper(a, b);
  res := ModHelper(product_str, m);
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
  if IsZero(sy) {
    res := ModHelper("1", sz);
  } else {
    var half := ModExp(sx, sy[0..|sy|-1], sz);
    var square := ModMul(half, half, sz);
    if sy[|sy|-1] == '1' {
      res := ModMul(square, sx, sz);
    } else {
      res := square;
    }
  }
}
// </vc-code>

