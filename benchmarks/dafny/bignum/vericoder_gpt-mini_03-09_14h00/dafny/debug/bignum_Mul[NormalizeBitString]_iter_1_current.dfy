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
method IntToBitString(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  ensures |s| > 0
  ensures |s| > 1 ==> s[0] != '0'
{
  if n == 0 {
    s := "0";
    return;
  }
  // compute k = number of bits of n (k = floor(log2(n)) + 1)
  var k := 0;
  var tmp := n;
  while tmp > 0
    decreases tmp
  {
    tmp := tmp / 2;
    k := k + 1;
  }

  // set p = 2^k (strictly greater than n)
  var p := 1;
  var i := 0;
  while i < k
    decreases k - i
  {
    p := p * 2;
    i := i + 1;
  }

  var rem := n;
  s := "";
  // invariant: ValidBitString(s), 0 <= rem < p, and Str2Int(s) * p + rem == n
  while p > 1
    decreases p
    invariant ValidBitString(s)
    invariant 0 <= rem < p
    invariant Str2Int(s) * p + rem == n
  {
    p := p / 2;
    if rem >= p {
      s := s + "1";
      rem := rem - p;
    } else {
      s := s + "0";
    }
  }
  // postconditions follow from invariants and construction
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
  // parse s1
  var a := 0;
  var i := 0;
  while i < |s1|
    decreases |s1| - i
    invariant 0 <= i <= |s1|
    invariant a == Str2Int(s1[0..i])
  {
    if s1[i] == '1' {
      a := 2 * a + 1;
    } else {
      a := 2 * a;
    }
    i := i + 1;
  }

  // parse s2
  var b := 0;
  i := 0;
  while i < |s2|
    decreases |s2| - i
    invariant 0 <= i <= |s2|
    invariant b == Str2Int(s2[0..i])
  {
    if s2[i] == '1' {
      b := 2 * b + 1;
    } else {
      b := 2 * b;
    }
    i := i + 1;
  }

  var p := a * b;
// </vc-code>

