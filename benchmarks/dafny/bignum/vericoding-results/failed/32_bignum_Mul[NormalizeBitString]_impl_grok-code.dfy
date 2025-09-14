ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Power2(k: nat): nat
  decreases k
{
  if k == 0 then 1 else 2 * Power2(k - 1)
}

method ShiftLeft(s: string, k: nat) returns (result: string)
  requires ValidBitString(s)
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(s) * Power2(k)
  decreases k
{
  if k == 0 {
    result := s;
  } else {
    var prev := ShiftLeft(s, k - 1);
    result := prev + "0";
  }
}

method NatToBitString(n: nat) returns (result: string)
  ensures ValidBitString(result)
  ensures Str2Int(result) == n
  decreases n
{
  if n == 0 {
    result := "0";
  } else {
    var rest := NatToBitString(n / 2);
    var next := if n % 2 == 0 then '0' else '1';
    result := rest + [next];
  }
}

method AddHelper(a: string, b: string) returns (result: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(a) + Str2Int(b)
{
  // Pad the shorter string with leading zeros (MSB side) to make them the same length
  var aPad: string;
  var bPad: string;
  if |a| >= |b| {
    aPad := a;
    var padLen := |a| - |b|;
    var zeros: string := "";
    var i := 0;
    while i < padLen
      invariant |zeros| == i
      invariant 0 <= i <= padLen
      invariant ValidBitString(zeros)
      decreases padLen - i
    {
      zeros := zeros + "0";
      i := i + 1;
    }
    bPad := zeros + b;
  } else {
    bPad := b;
    var padLen := |b| - |a|;
    var zeros: string := "";
    var i := 0;
    while i < padLen
      invariant |zeros| == i
      invariant 0 <= i <= padLen
      invariant ValidBitString(zeros)
      decreases padLen - i
    {
      zeros := zeros + "0";
      i := i + 1;
    }
    aPad := zeros + a;
  }

  // Now aPad and bPad have the same length
  var len := |aPad|;

  // Perform binary addition from LSB (rightmost, index len-1) to MSB (index 0)
  var carry := 0;
  var sumStr: seq<char> := [];
  var i := len - 1;
  while i >= 0
    invariant 0 <= i + 1 <= len
    invariant |sumStr| == len - 1 - i
    invariant ValidBitString(sumStr)
    invariant carry == 0 || carry == 1
    decreases i
  {
    var bit1 := if aPad[i] == '1' then 1 else 0;
    var bit2 := if bPad[i] == '1' then 1 else 0;
    var sum := bit1 + bit2 + carry;
    var nextBit: char := if sum % 2 == 0 then '0' else '1';
    carry := sum / 2;
    sumStr := [nextBit] + sumStr;
    i := i - 1;
  }

  // If there's a final carry, prepend it
  if carry == 1 {
    sumStr := ['1'] + sumStr;
  }

  var tempResult := sumStr;
  result := NormalizeBitString(tempResult);
}

method MulHelper(s1: string, s2: string) returns (result: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(s1) * Str2Int(s2)
  decreases |s2|
{
  if |s2| == 0 {
    result := "0";
  } else {
    var left := MulHelper(s1, s2[0..|s2|-1]);
    var right := if s2[|s2|-1] == '1' then s1 else "0";
    var leftShifted := left + "0";
    var sum := AddHelper(leftShifted, right);
    result := NormalizeBitString(sum);
  }
}

method NormalizeBitString(s: string) returns (t: string)
  requires ValidBitString(s)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures Str2Int(s) == Str2Int(t)
  decreases |s|
{
  if |s| == 0 {
    t := "0";
  } else {
    if s[0] == '1' {
      t := s;
    } else {
      var next := NormalizeBitString(s[1..]);
      if |next| > 1 {
        t := next;
      } else if Str2Int(next) == 0 {
        t := "0";
      } else {
        t := next;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var ret := MulHelper(s1, s2);
  res := NormalizeBitString(ret);
}
// </vc-code>

