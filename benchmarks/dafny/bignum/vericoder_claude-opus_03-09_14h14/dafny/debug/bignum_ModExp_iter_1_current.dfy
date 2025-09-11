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

// <vc-helpers>
method Int2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  if n == 0 {
    s := "0";
  } else {
    var temp := n;
    s := "";
    while temp > 0
      invariant 0 <= temp <= n
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

method StrToInt(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
  {
    n := n * 2;
    if s[i] == '1' {
      n := n + 1;
    }
    i := i + 1;
  }
}

method IsEven(s: string) returns (even: bool)
  requires ValidBitString(s)
  requires |s| > 0
  ensures even == (Str2Int(s) % 2 == 0)
{
  even := (s[|s|-1] == '0');
}

method DivBy2(s: string) returns (res: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) / 2
{
  if |s| == 1 {
    res := "0";
  } else {
    res := s[0..|s|-1];
  }
}

method ModMult(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sz) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(sx) * Str2Int(sy)) % Str2Int(sz)
{
  var x := StrToInt(sx);
  var y := StrToInt(sy);
  var z := StrToInt(sz);
  var prod := (x * y) % z;
  res := Int2Str(prod);
}

lemma ExpEvenPower(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    assert Exp_int(x, 2) == x * x * 1;
    assert Exp_int(x * x, 1) == x * x * 1;
  } else {
    var half := y / 2;
    assert y == 2 * half;
    assert Exp_int(x, y) == Exp_int(x, 2 * half);
  }
}

lemma ExpOddPower(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
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
  if |sy| == 1 && sy[0] == '0' {
    res := "1";
    return;
  }
  
  var isEven := IsEven(sy);
  
  if isEven {
    var halfY := DivBy2(sy);
    var temp := ModExp(sx, halfY, sz);
    res := ModMult(temp, temp, sz);
  } else {
    if |sy| == 1 && sy[0] == '1' {
      var x := StrToInt(sx);
      var z := StrToInt(sz);
      var r := x % z;
      res := Int2Str(r);
    } else {
      var sy_minus_1_int := StrToInt(sy);
      sy_minus_1_int := sy_minus_1_int - 1;
      var sy_minus_1 := Int2Str(sy_minus_1_int);
      var halfY := DivBy2(sy_minus_1);
      var temp := ModExp(sx, halfY, sz);
      var temp_squared := ModMult(temp, temp, sz);
      res := ModMult(sx, temp_squared, sz);
    }
  }
}
// </vc-code>

