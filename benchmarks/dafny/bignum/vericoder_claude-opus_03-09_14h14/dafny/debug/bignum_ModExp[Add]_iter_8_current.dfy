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
lemma Str2IntDivTwo(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s[0..|s|-1]) == Str2Int(s) / 2
{
  if |s| == 1 {
    assert s[0..|s|-1] == "";
    assert Str2Int("") == 0;
    assert s[0] == '0' || s[0] == '1';
    if s[0] == '0' {
      assert Str2Int(s) == 0;
      assert Str2Int(s) / 2 == 0;
    } else {
      assert Str2Int(s) == 1;
      assert Str2Int(s) / 2 == 0;
    }
  }
}

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
    Str2IntDivTwo(s);
  }
}

method SubtractOne(s: string) returns (res: string)
  requires ValidBitString(s)
  requires Str2Int(s) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) - 1
{
  if s == "1" {
    res := "0";
    return;
  }
  
  var chars := [];
  var i := |s| - 1;
  var borrow := true;
  
  while i >= 0
    invariant -1 <= i < |s|
    invariant |chars| == |s| - 1 - i
  {
    if borrow {
      if s[i] == '1' {
        chars := ['0'] + chars;
        borrow := false;
      } else {
        chars := ['1'] + chars;
      }
    } else {
      chars := [s[i]] + chars;
    }
    i := i - 1;
  }
  
  res := "";
  i := 0;
  while i < |chars|
    invariant 0 <= i <= |chars|
    invariant |res| == i
    invariant ValidBitString(res)
  {
    res := res + [chars[i]];
    i := i + 1;
  }
  
  // Remove leading zeros
  i := 0;
  while i < |res| - 1 && res[i] == '0'
    invariant 0 <= i < |res|
  {
    i := i + 1;
  }
  if i > 0 {
    res := res[i..];
  }
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var carry := '0';
  var result := [];
  var i1 := |s1| - 1;
  var i2 := |s2| - 1;
  
  while i1 >= 0 || i2 >= 0 || carry == '1'
    invariant -1 <= i1 < |s1|
    invariant -1 <= i2 < |s2|
    invariant carry == '0' || carry == '1'
  {
    var bit1 := if i1 >= 0 then s1[i1] else '0';
    var bit2 := if i2 >= 0 then s2[i2] else '0';
    
    var sum := (if bit1 == '1' then 1 else 0) + 
               (if bit2 == '1' then 1 else 0) + 
               (if carry == '1' then 1 else 0);
    
    result := [if sum % 2 == 1 then '1' else '0'] + result;
    carry := if sum >= 2 then '1' else '0';
    
    if i1 >= 0 { i1 := i1 - 1; }
    if i2 >= 0 { i2 := i2 - 1; }
  }
  
  res := "";
  var j := 0;
  while j < |result|
    invariant 0 <= j <= |result|
    invariant ValidBitString(res)
  {
    res := res + [result[j]];
    j := j + 1;
  }
  
  // Remove leading zeros
  j := 0;
  while j < |res| - 1 && res[j] == '0'
    invariant 0 <= j < |res|
  {
    j := j + 1;
  }
  if j > 0 {
    res := res[j..];
  }
  if |res| == 0 {
    res := "0";
  }
}

method Subtract(sa: string, sb: string) returns (res: string)
  requires ValidBitString(sa) && ValidBitString(sb)
  requires Str2Int(sa) >= Str2Int(sb)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(sa) - Str2Int(sb)
{
  if sb == "0" || sa == sb {
    if sa == sb {
      res := "0";
    } else {
      res := sa;
    }
    return;
  }
  
  var borrow := '0';
  var result := [];
  var i1 := |sa| - 1;
  var i2 := |sb| - 1;
  
  while i1 >= 0
    invariant -1 <= i1 < |sa|
    invariant -1 <= i2 < |sb|
    invariant borrow == '0' || borrow == '1'
  {
    var bit1 := sa[i1];
    var bit2 := if i2 >= 0 then sb[i2] else '0';
    
    var val1 := if bit1 == '1' then 1 else 0;
    var val2 := if bit2 == '1' then 1 else 0;
    var borrowVal := if borrow == '1' then 1 else 0;
    
    var diff := val1 - val2 - borrowVal;
    if diff < 0 {
      diff := diff + 2;
      borrow := '1';
    } else {
      borrow := '0';
    }
    
    result := [if diff == 1 then '1' else '0'] + result;
    
    i1 := i1 - 1;
    if i2 >= 0 { i2 := i2 - 1; }
  }
  
  res := "";
  var j := 0;
  while j < |result|
    invariant 0 <= j <= |result|
    invariant ValidBitString(res)
  {
    res := res + [result[j]];
    j := j + 1;
  }
  
  // Remove leading zeros
  j := 0;
  while j < |res| - 1 && res[j] == '0'
    invariant 0 <= j < |res|
  {
    j := j + 1;
  }
  if j > 0 {
    res := res[j..];
  }
  if |res| == 0 {
    res := "0";
  }
}

method ModMul(sa: string, sb: string, sm: string) returns (res: string)
  requires ValidBitString(sa) && ValidBitString(sb) && ValidBitString(sm)
  requires Str2Int(sm) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(sa) * Str2Int(sb)) % Str2Int(sm)
{
  res := "0";
  var a := sa;
  var b := sb;
  
  while true
    invariant ValidBitString(res)
    invariant ValidBitString(a)
    invariant ValidBitString(b)
    decreases Str2Int(b)
  {
    var bIsZero := IsZero(b);
    if bIsZero {
      break;
    }
    
    var bIsEven := IsEven(b);
    if !bIsEven {
      res := AddMod(res, a, sm);
    }
    
    a := AddMod(a, a, sm);
    b := DivideByTwo(b);
  }
}

method AddMod(sa: string, sb: string, sm: string) returns (res: string)
  requires ValidBitString(sa) && ValidBitString(sb) && ValidBitString(sm)
  requires Str2Int(sm) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(sa) + Str2Int(sb)) % Str2Int(sm)
{
  var sum := Add(sa, sb);
  res := ModReduce(sum, sm);
}

method ModReduce(s: string, sm: string) returns (res: string)
  requires ValidBitString(s) && ValidBitString(sm)
  requires Str2Int(sm) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) % Str2Int(sm)
{
  res := s;
  while true
    invariant ValidBitString(res)
    invariant Str2Int(res) % Str2Int(sm) == Str2Int(s) % Str2Int(sm)
    decreases Str2Int(res)
  {
    var cmp := Compare(res, sm);
    if cmp < 0 {
      break;
    }
    res := Subtract(res, sm);
  }
}

method Compare(sa: string, sb: string) returns (cmp: int)
  requires ValidBitString(sa) && ValidBitString(sb)
  ensures cmp < 0 <==> Str2Int(sa) < Str2Int(sb)
  ensures cmp == 0 <==> Str2Int(sa) == Str2Int(sb)
  ensures cmp > 0 <==> Str2Int(sa) > Str2Int(sb)
{
  if |sa| < |sb| {
    cmp := -1;
  } else if |sa| > |sb| {
    cmp := 1;
  } else {
    cmp := 0;
    var i := 0;
    while i < |sa|
      invariant 0 <= i <= |sa|
    {
      if sa[i] < sb[i] {
        cmp := -1;
        break;
      } else if sa[i] > sb[i] {
        cmp := 1;
        break;
      }
      i := i + 1;
    }
  }
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
  
  while true
    invariant ValidBitString(base)
    invariant ValidBitString(exp)
    invariant ValidBitString(res)
    decreases Str2Int(exp)
  {
    var expIsZero := IsZero(exp);
    if expIsZero {
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
  }
}
// </vc-code>

