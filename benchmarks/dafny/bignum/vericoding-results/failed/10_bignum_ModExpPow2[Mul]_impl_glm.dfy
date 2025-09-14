ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  if |s1| == 0 || |s2| == 0 {
    res := "0";
  } else {
    var last1 := s1[|s1|-1];
    var last2 := s2[|s2|-1];
    var rest1 := s1[0..|s1|-1];
    var rest2 := s2[0..|s2|-1];
    var temp1 := Mul(rest1, s2);
    var temp2 := Mul(s1, rest2);
    var temp3 := if last1 == '1' && last2 == '1' then "1" else "0";
    
    var sum1 := Add(temp1, temp2);
    var sum2 := Add(sum1, temp3);
    res := sum2;
  }
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  if |s1| == 0 {
    res := s2;
  } else if |s2| == 0 {
    res := s1;
  } else {
    var last1 := s1[|s1|-1];
    var last2 := s2[|s2|-1];
    var rest1 := s1[0..|s1|-1];
    var rest2 := s2[0..|s2|-1];
    var temp := Add(rest1, rest2);
    var bit, carried, rest := last1, last2, temp;
    
    if |temp| > 0 {
      carried := temp[|temp|-1];
      rest := temp[0..|temp|-1];
    } else {
      carried := '0';
      rest := "";
    }
    
    var sum := if bit == '1' && last2 == '1' then '0' else 
               if bit == '1' || last2 == '1' then '1' else '0';
    
    if carried == '0' {
      res := rest + sum;
    } else {
      var newTemp := Add(rest, "1");
      res := newTemp + sum;
    }
  }
}

method Mod(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)
{
  if |s1| == 0 {
    res := "0";
  } else if Str2Int(s1) < Str2Int(s2) {
    res := s1;
  } else {
    var last := s1[|s1|-1];
    var rest := s1[0..|s1|-1];
    var temp := Mod(rest, s2);
    var doubled := Add(temp, temp);
    var withLast := if last == '1' then Add(doubled, "1") else doubled;
    
    if Str2Int(withLast) >= Str2Int(s2) {
      res := Mod(Sub(withLast, s2), s2);
    } else {
      res := withLast;
    }
  }
}

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  if |s2| == 0 {
    res := s1;
  } else {
    var last1 := s1[|s1|-1];
    var last2 := s2[|s2|-1];
    var rest1 := s1[0..|s1|-1];
    var rest2 := s2[0..|s2|-1];
    
    if last1 == '1' && last2 == '1' {
      res := Sub(rest1, rest2) + '0';
    } else if last1 == '0' && last2 == '1' {
      var borrow := Sub(rest1, "1");
      res := Sub(borrow, rest2) + '1';
    } else {
      res := Sub(rest1, rest2) + last1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    if Str2Int(sy) == 0 {
      res := "1";
    } else {
      res := sx;
    }
  } else {
    var temp := ModExpPow2(sx, sy, n - 1, sz);
    var squared := Mul(temp, temp);
    var modded := Mod(squared, sz);
    res := modded;
  }
}
// </vc-code>

