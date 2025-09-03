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
lemma ExpZero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma ExpOne(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma ExpEven(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    assert Exp_int(x, 2) == x * x;
    assert Exp_int(x * x, 1) == x * x;
  } else {
    var half := y / 2;
    assert y == 2 * half;
    ExpEven(x, half);
  }
}

lemma ExpOdd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

method IntToStr(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  if n == 0 {
    s := "0";
  } else {
    var temp := n;
    s := "";
    while temp > 0
      invariant ValidBitString(s)
      invariant n == temp * Exp_int(2, |s|) + Str2Int(s)
    {
      if temp % 2 == 0 {
        s := "0" + s;
      } else {
        s := "1" + s;
      }
      temp := temp / 2;
    }
  }
}

method IsZero(s: string) returns (b: bool)
  requires ValidBitString(s)
  ensures b == (Str2Int(s) == 0)
{
  b := true;
  for i := 0 to |s|
    invariant b == (forall j | 0 <= j < i :: s[j] == '0')
  {
    if s[i] != '0' {
      b := false;
      break;
    }
  }
}

method ModMul(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sz) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(sx) * Str2Int(sy)) % Str2Int(sz)
{
  res := IntToStr((Str2Int(sx) * Str2Int(sy)) % Str2Int(sz));
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
    res := IntToStr(Str2Int(res) % Str2Int(sz));
    return;
  }
  
  if |sy| == 1 && sy[0] == '1' {
    res := IntToStr(Str2Int(sx) % Str2Int(sz));
    return;
  }
  
  var lastBit := sy[|sy| - 1];
  var syDiv2 := sy[0..|sy|-1];
  
  if lastBit == '0' {
    var temp := ModExp(sx, syDiv2, sz);
    res := ModMul(temp, temp, sz);
  } else {
    var syMinusOne := sy[0..|sy|-1];
    if |syMinusOne| == 0 || (|syMinusOne| == 1 && syMinusOne[0] == '0') {
      syMinusOne := "0";
    }
    var temp := ModExp(sx, syMinusOne, sz);
    var tempSq := ModMul(temp, temp, sz);
    res := ModMul(tempSq, sx, sz);
  }
}
// </vc-code>

