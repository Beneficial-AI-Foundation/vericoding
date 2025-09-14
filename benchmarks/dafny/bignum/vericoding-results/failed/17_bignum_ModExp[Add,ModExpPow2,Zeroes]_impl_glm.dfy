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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
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
    var c := '0';
    var sum := "";
    var i := |s1| - 1;
    var j := |s2| - 1;
    while i >= 0 || j >= 0 || c == '1'
      invariant ValidBitString(sum)
      invariant (c == '0' || c == '1')
      invariant Str2Int(sum) + (if c == '1' then 1 else 0) * Exp_int(2, |sum|) == Str2Int(s1[0..i+1]) + Str2Int(s2[0..j+1])
      decreases i + j
    {
      var a := if i >= 0 then s1[i] else '0';
      var b := if j >= 0 then s2[j] else '0';
      var count := (if a == '1' then 1 else 0) + (if b == '1' then 1 else 0) + (if c == '1' then 1 else 0);
      c := if count >= 2 then '1' else '0';
      sum := (if count % 2 == 1 then "1" else "0") + sum;
      i := i - 1;
      j := j - 1;
    }
    res := sum;
  }
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  if n == 0 {
    s := "";
  } else {
    var tail := Zeros(n-1);
    s := "0" + tail;
  }
}

method Multiply(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  if |s1| == 0 || |s2| == 0 {
    res := "";
  } else if Str2Int(s1) == 0 || Str2Int(s2) == 0 {
    res := "";
  } else {
    var sum := "";
    var shift := Zeros(0);
    for i := |s2|-1 downto 0
      invariant ValidBitString(shift)
      invariant ValidBitString(sum)
      invariant Str2Int(sum) + Str2Int(shift) * Str2Int(s2[i+1..|s2|]) * Str2Int(s1) == Str2Int(s1) * Str2Int(s2[0..i+1])
    {
      if s2[i] == '1' {
        var addend := s1 + shift;
        sum := Add(sum, addend);
      }
      shift := shift + "0";
    }
    res := sum;
  }
}

method Mod(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)
{
  if Str2Int(s1) < Str2Int(s2) {
    res := s1;
  } else {
    var diff := Subtract(s1, s2);
    res := Mod(diff, s2);
  }
}

method Subtract(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  var diff := "";
  var borrow := 0;
  var i := |s1| - 1;
  var j := |s2| - 1;
  while i >= 0
    invariant ValidBitString(diff)
    invariant 0 <= borrow <= 1
    invariant Str2Int(diff) - borrow * Exp_int(2, |diff|) == Str2Int(s1[0..i+1]) - Str2Int(s2[0..j+1])
    decreases i
  {
    var a := if i >= 0 then (if s1[i] == '1' then 1 else 0) else 0;
    var b := if j >= 0 then (if s2[j] == '1' then 1 else 0) else 0;
    var d := a - b - borrow;
    borrow := if d < 0 then 1 else 0;
    diff := (if d % 2 == 1 then "1" else "0") + diff;
    i := i - 1;
    j := j - 1;
  }
  var firstNonZero := 0;
  while firstNonZero < |diff| - 1 && diff[firstNonZero] == '0'
    decreases |diff| - firstNonZero
  {
    firstNonZero := firstNonZero + 1;
  }
  res := diff[firstNonZero..|diff|];
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
  if |sy| == 1 {
    if sy[0] == '0' {
      var one := "1";
      res := Mod(one, sz);
    } else {
      res := Mod(sx, sz);
    }
  } else {
    var halved := sy[0..|sy|-1];
    var sub := ModExp(sx, halved, sz);
    var squared := Multiply(sub, sub);
    if sy[|sy|-1] == '0' {
      res := Mod(squared, sz);
    } else {
      var multiplied := Multiply(squared, sx);
      res := Mod(multiplied, sz);
    }
  }
}
// </vc-code>

