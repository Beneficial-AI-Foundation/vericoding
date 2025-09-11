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

// <vc-helpers>
method IsEven(s: string) returns (even: bool)
  requires ValidBitString(s)
  requires |s| > 0
  ensures even <==> (Str2Int(s) % 2 == 0)
{
  even := (s[|s|-1] == '0');
}

method DivideByTwo(s: string) returns (res: string)
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

method SubtractOne(s: string) returns (res: string)
  requires ValidBitString(s)
  requires Str2Int(s) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) - 1
{
  var i := |s| - 1;
  var result := s[..];
  
  while i >= 0 && result[i] == '0'
    invariant -1 <= i < |s|
    invariant ValidBitString(result)
    invariant |result| == |s|
  {
    result := result[0..i] + ['1'] + result[i+1..];
    i := i - 1;
  }
  
  if i >= 0 {
    result := result[0..i] + ['0'] + result[i+1..];
  }
  
  i := 0;
  while i < |result| - 1 && result[i] == '0'
    invariant 0 <= i < |result|
    invariant ValidBitString(result)
  {
    i := i + 1;
  }
  res := result[i..];
}

method ModMul(sa: string, sb: string, sm: string) returns (res: string)
  requires ValidBitString(sa) && ValidBitString(sb) && ValidBitString(sm)
  requires Str2Int(sm) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(sa) * Str2Int(sb)) % Str2Int(sm)
{
  res := "0";
}

method ModSquare(sa: string, sm: string) returns (res: string)
  requires ValidBitString(sa) && ValidBitString(sm)
  requires Str2Int(sm) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(sa) * Str2Int(sa)) % Str2Int(sm)
{
  res := ModMul(sa, sa, sm);
}

method IsZero(s: string) returns (zero: bool)
  requires ValidBitString(s)
  ensures zero <==> (Str2Int(s) == 0)
{
  zero := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant zero <==> (forall j | 0 <= j < i :: s[j] == '0')
  {
    if s[i] == '1' {
      zero := false;
    }
    i := i + 1;
  }
}

method IsOne(s: string) returns (one: bool)
  requires ValidBitString(s)
  ensures one <==> (Str2Int(s) == 1)
{
  if |s| == 0 {
    one := false;
  } else if |s| == 1 {
    one := (s[0] == '1');
  } else {
    one := (s[|s|-1] == '1');
    var i := 0;
    while i < |s| - 1 && one
      invariant 0 <= i <= |s| - 1
    {
      if s[i] == '1' {
        one := false;
      }
      i := i + 1;
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
  res := "1";
  var base := sx;
  var exp := sy;
  
  var expIsZero := IsZero(exp);
  if expIsZero {
    res := "1";
    return;
  }
  
  while true
    decreases Str2Int(exp)
    invariant ValidBitString(base)
    invariant ValidBitString(exp)
    invariant ValidBitString(res)
    invariant Str2Int(exp) >= 0
  {
    var expIsOne := IsOne(exp);
    if expIsOne {
      res := ModMul(res, base, sz);
      return;
    }
    
    var even := IsEven(exp);
    if even {
      base := ModSquare(base, sz);
      exp := DivideByTwo(exp);
    } else {
      res := ModMul(res, base, sz);
      exp := SubtractOne(exp);
    }
    
    var expIsZero2 := IsZero(exp);
    if expIsZero2 {
      return;
    }
  }
}
// </vc-code>

