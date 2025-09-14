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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
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
ghost function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "0" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var s1 := s1;
  var s2 := s2;
  var l1 := |s1|;
  var l2 := |s2|;

  // Padding to make lengths equal
  var max_len := if l1 > l2 then l1 else l2;

  if l1 < max_len {
    var pad := "";
    for i := 0 to max_len - l1 - 1
      invariant |pad| == i
    {
      pad := "0" + pad;
    }
    s1 := pad + s1;
  }

  if l2 < max_len {
    var pad := "";
    for i := 0 to max_len - l2 - 1
      invariant |pad| == i
    {
      pad := "0" + pad;
    }
    s2 := pad + s2;
  }

  var carry := 0;
  var result := "";
  var i := max_len;
  while i > 0
    invariant i <= max_len + 1
    invariant ValidBitString(result)
    invariant carry == 0 || carry == 1
    decreases i
  {
    i := i - 1;
    var a := if s1[i] == '1' then 1 else 0;
    var b := if s2[i] == '1' then 1 else 0;
    var sum := a + b + carry;
    var digit := if sum % 2 == 1 then '1' else '0';
    carry := sum / 2;
    result := digit + result;
  }

  if carry == 1 {
    result := '1' + result;
  }

  // Remove leading zeros
  if result == "" {
    return "0";
  }
  var start := 0;
  while start < |result| - 1 && result[start] == '0'
    invariant start <= |result|
    decreases |result| - start
  {
    start := start + 1;
  }
  if start == |result| {
    return "0";
  }
  return result[start..];
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  var res := "";
  for i := 0 to n - 1
    invariant |res| == i
    invariant ValidBitString(res) && AllZero(res)
  {
    res := res + '0';
  }
  return res;
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  if s2 == "" || s2 == "0" {
    return "0";
  }
  var result := "0";
  var temp := s1;
  var i := 0;
  var len_s2 := |s2|;
  while i < len_s2
    invariant i <= len_s2
    invariant ValidBitString(result) && ValidBitString(temp)
    invariant |temp| == |s1| + i
    invariant Str2Int(result) == Str2Int(s1) * Str2Int(s2[..i])
    decreases len_s2 - i
  {
    if s2[len_s2 - 1 - i] == '1' {
      result := Add(result, temp);
    }
    temp := temp + '0';
    i := i + 1;
  }

  // Remove leading zeros
  if result == "" {
    return "0";
  }
  var j := 0;
  while j < |result| - 1 && result[j] == '0'
    invariant j <= |result|
    decreases |result| - j
  {
    j := j + 1;
  }
  if j == |result| {
    return "0";
  }
  return result[j..];
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  var d1 := Str2Int(dividend);
  var d2 := Str2Int(divisor);
  var quot := d1 / d2;
  var rem := d1 % d2;
  var qs := Int2Str(quot);
  var rs := Int2Str(rem);
  return qs, rs;
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
    if sy == "0" {
      var q, r := DivMod("1", sz);
      return r;
    } else {
      var q, r := DivMod(sx, sz);
      return r;
    }
  } else {
    var half := sy[..|sy|-1];
    var sq := Mul(sx, sx);
    var exp_half := ModExp(sq, half, sz);
    if sy[|sy|-1] == '0' {
      return exp_half;
    } else {
      var prod := Mul(sx, exp_half);
      var q2, res := DivMod(prod, sz);
      return res;
    }
  }
}
// </vc-code>

