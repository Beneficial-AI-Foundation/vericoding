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
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var aRev := Reverse(s1);
  var bRev := Reverse(s2);
  var carry := 0;
  var resultRev := "";
  var i := 0;
  while i < |aRev| || i < |bRev| || carry == 1
    invariant 0 <= i <= |aRev| || 0 <= i <= |bRev|
    invariant carry == 0 || carry == 1
  {
    var digitA := if i < |aRev| then (if aRev[i] == '1' then 1 else 0) else 0;
    var digitB := if i < |bRev| then (if bRev[i] == '1' then 1 else 0) else 0;
    var sum := digitA + digitB + carry;
    carry := sum / 2;
    var bit := sum % 2;
    resultRev := resultRev + (if bit == 1 then "1" else "0");
    i := i + 1;
  }
  res := Reverse(resultRev);
}

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  if n == 0 {
    if sy == "0" {
      res := "1";
    } else {
      res := Mod(sx, sz);
    }
  } else {
    var halfPower := ModExpPow2(sx, "1" + (seq(n-1, i => '0')), n-1, sz);
    res := Mul(halfPower, halfPower);
    res := Mod(res, sz);
  }
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  if s1 == "0" || s2 == "0" {
    res := "0";
  } else {
    var sum := "0";
    var a := Reverse(s1);
    var i := 0;
    while i < |a|
      invariant 0 <= i <= |a|
      invariant ValidBitString(sum)
      invariant Str2Int(sum) == Str2Int(s1) * Str2Int(s2[0..|a|-i])
    {
      if a[i] == '1' {
        var shifted := s2 + (seq(i, j => '0'));
        sum := Add(sum, shifted);
      }
      i := i + 1;
    }
    res := sum;
  }
}

method LessThan(a: string, b: string) returns (lt: bool)
  requires ValidBitString(a) && ValidBitString(b)
  ensures lt <==> Str2Int(a) < Str2Int(b)
{
  if |a| < |b| {
    return true;
  } else if |a| > |b| {
    return false;
  } else {
    var i := 0;
    while i < |a| 
      invariant 0 <= i <= |a|
      invariant forall j :: 0 <= j < i ==> a[j] == b[j]
    {
      if a[i] == '1' && b[i] == '0' {
        return false;
      } else if a[i] == '0' && b[i] == '1' {
        return true;
      }
      i := i + 1;
    }
    return false;
  }
}

method Reverse(s: string) returns (r: string)
  ensures |r| == |s|
  ensures forall i :: 0 <= i < |s| ==> r[i] == s[|s|-1-i]
{
  r := "";
  var i := |s| - 1;
  while i >= 0 
    invariant 0 <= i+1 <= |s|
    invariant |r| == |s| - (i+1)
    invariant forall j :: 0 <= j < |r| ==> r[j] == s[|s|-1-j]
  {
    r := r + [s[i]];
    i := i - 1;
  }
}

method Subtract(a: string, b: string) returns (r: string)
  requires ValidBitString(a) && ValidBitString(b)
  requires Str2Int(a) >= Str2Int(b)
  ensures ValidBitString(r)
  ensures Str2Int(r) == Str2Int(a) - Str2Int(b)
{
  var aRev := Reverse(a);
  var bRev := Reverse(b);
  var borrow := 0;
  var resultRev := "";
  var i := 0;
  while i < |aRev| || i < |bRev| 
    invariant 0 <= i <= |aRev| || 0 <= i <= |bRev|
    invariant borrow == 0 || borrow == 1
  {
    var digitA := if i < |aRev| then (if aRev[i] == '1' then 1 else 0) else 0;
    var digitB := if i < |bRev| then (if bRev[i] == '1' then 1 else 0) else 0;
    var diff := digitA - digitB - borrow;
    borrow := if diff < 0 then 1 else 0;
    diff := if diff < 0 then diff + 2 else diff;
    resultRev := resultRev + (if diff == 1 then "1" else "0");
    i := i + 1;
  }
  var j := |resultRev| - 1;
  while j > 0 && resultRev[j] == '0' {
    j := j - 1;
  }
  resultRev := resultRev[0..j+1];
  r := Reverse(resultRev);
}

method Mod(a: string, b: string) returns (r: string)
  requires ValidBitString(a) && ValidBitString(b)
  requires Str2Int(b) > 0
  ensures ValidBitString(r)
  ensures Str2Int(r) == Str2Int(a) % Str2Int(b)
  ensures Str2Int(r) < Str2Int(b)
{
  r := a;
  while true 
    invariant ValidBitString(r)
    invariant Str2Int(r) <= Str2Int(a)
    decreases Str2Int(r)
  {
    var lt := LessThan(b, r);
    if lt || r == b {
      r := Subtract(r, b);
    } else {
      break;
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
  var result := "1";
  var base := sx;
  var i := 0;
  while i < |sy|
    invariant ValidBitString(result)
    invariant ValidBitString(base)
    invariant Str2Int(result) == Exp_int(Str2Int(sx), Str2Int(sy[0..i])) % Str2Int(sz)
    decreases |sy| - i
  {
    result := ModExpPow2(result, "10", 1, sz);
    if sy[i] == '1' {
      var product := Mul(result, base);
      result := Mod(product, sz);
    }
    base := ModExpPow2(base, "10", 1, sz);
    i := i + 1;
  }
}
// </vc-code>

