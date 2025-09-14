ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
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
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method NormalizeBitString(s: string) returns (t: string)
  requires ValidBitString(s)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures Str2Int(s) == Str2Int(t)
{
  var i := 0;
  while i < |s| && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant forall k | 0 <= k < i :: s[k] == '0'
  {
    i := i + 1;
  }
  if i == |s| {
    t := "0";
  } else {
    t := s[i..];
  }
}

lemma Str2IntLeadingZeros(zeros: string, rest: string)
  requires ValidBitString(zeros + rest)
  requires forall i | 0 <= i < |zeros| :: zeros[i] == '0'
  ensures Str2Int(zeros + rest) == Str2Int(rest)
  decreases |zeros|
{
  if |zeros| == 0 { }
  else {
    Str2IntLeadingZeros(zeros[1..], rest);
  }
}

lemma Str2IntAllZeros(s: string)
  requires forall i | 0 <= i < |s| :: s[i] == '0' && ValidBitString(s)
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 { }
  else {
    Str2IntAllZeros(s[1..]);
    assert Str2Int(s) == 2 * Str2Int(s[1..]) + (if s[|s|-1] == '0' then 0 else 1);
    if s[|s|-1] == '0' {
      assert Str2Int(s) == 2 * Str2Int(s[1..]);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var n1 := NormalizeBitString(s1);
  var n2 := NormalizeBitString(s2);
  var len1 := |n1| as int;
  var len2 := |n2| as int;
  var len := if len1 > len2 then len1 else len2;
  var extra1 := len - len1;
  var extra2 := len - len2;
  var pad1 := "";
  for _ := 0 to extra1 {
    pad1 := pad1 + "0";
  }
  var p1 := pad1 + n1;
  var pad2 := "";
  for _ := 0 to extra2 {
    pad2 := pad2 + "0";
  }
  var p2 := pad2 + n2;
  var resultstr := "";
  var borrow := 0;
  for pos := len - 1 downto 0
    invariant borrow == 0 || borrow == 1
    invariant ValidBitString(resultstr + p1[pos+1..])  // partial validity
  {
    var b1 := if p1[pos] == '1' then 1 else 0;
    var b2 := if p2[pos] == '1' then 1 else 0;
    var diff := b1 - b2 - borrow;
    if diff < 0 {
      diff := diff + 2;
      borrow := 1;
    } else {
      borrow := 0;
    }
    var ch := if diff == 1 then "1" else "0";
    resultstr := ch + resultstr;
  }
  assert borrow == 0;  // since Str2Int(s1) >= Str2Int(s2)
  res := NormalizeBitString(resultstr);
}
// </vc-code>

