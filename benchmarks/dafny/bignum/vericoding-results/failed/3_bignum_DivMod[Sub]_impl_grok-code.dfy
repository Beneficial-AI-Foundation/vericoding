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

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
// Helper methods for binary string operations

function SeqPadZero(head: nat, s: string): string {
  seq(head, i => '0') + s
}

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  var len := if |s1| > |s2| then |s1| else |s2| + 1;
  var A := SeqPadZero(len - |s1|, s1);
  var B := SeqPadZero(len - |s2|, s2);
  var borrow := 0;
  var c := "";
  var i := len - 1;
  while i >= 0
    invariant 0 <= borrow <= 1
    invariant -1 <= i <= len - 1 && ((i == -1) ==> borrow == 0)
    invariant |c| == len - (i + 1)
    invariant ValidBitString(c)
    invariant borrow == 0 || exists k :: 0 <= k < len - i && c[k] == if borrow == 1 then '1' else '0'
  {
    var bitA := if A[i] == '1' then 1 else 0;
    var bitB := if B[i] == '1' then 1 else 0;
    var diff := bitA - bitB - borrow;
    if diff >= 0 {
      c := (if diff == 0 then "0" else "1") + c;
      borrow := 0;
    } else {
      c := (if diff == 2 then "0" else "1") + c;
      borrow := 1;
    }
    i := i - 1;
  }
  // Remove leading zeros
  var start := 0;
  while start < |c| && (start < |c| - 1 ==> c[start] == '0') {
    start := start + 1;
  }
  res := c[start..];
}

method Add(a: string, b: string) returns (c: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures ValidBitString(c)
  ensures Str2Int(c) == Str2Int(a) + Str2Int(b)
{
  var len := |a| + |b| + 1;
  var A := SeqPadZero(len - |a|, a);
  var B := SeqPadZero(len - |b|, b);
  var carry := 0;
  var resSeq := "";
  var i := len - 1;
  while i >= 0
    invariant 0 <= carry <= 1
    invariant |resSeq| == len - (i + 1)
    invariant ValidBitString(resSeq)
    invariant Str2Int(resSeq) + pow2(|resSeq|) * carry == Str2Int(A[(i+1)..len]) + Str2Int(B[(i+1)..len])
  {
    var bitA := if A[i] == '1' then 1 else 0;
    var bitB := if B[i] == '1' then 1 else 0;
    var sum := bitA + bitB + carry;
    resSeq := (if sum % 2 == 0 then "0" else "1") + resSeq;
    carry := sum / 2;
    i := i - 1;
  }
  if carry == 1 {
    resSeq := "1" + resSeq;
  }
  // Remove leading zeros
  var start := 0;
  while start < |resSeq| && (start < |resSeq| - 1 ==> resSeq[start] == '0') {
    start := start + 1;
  }
  c := resSeq[start..];
}
// </vc-helpers>

// <vc-spec>
method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
// </vc-spec>
// <vc-code>
{
  var q := "";
  var rem := dividend;
  ghost var remVal := Str2Int(rem);
  ghost var divisorVal := Str2Int(divisor);
  ghost var dividendVal := remVal;
  ghost var qVal := 0;
  while remVal >= divisorVal
    decreases remVal
    invariant remVal == Str2Int(rem)
    invariant qVal == Str2Int(q)
    invariant divisorVal == Str2Int(divisor)
    invariant ValidBitString(q) && ValidBitString(rem)
    invariant 0 <= remVal <= dividendVal
    invariant qVal <= dividendVal
    invariant qVal == dividendVal / divisorVal - remVal / divisorVal
    invariant dividendVal == qVal * divisorVal + remVal
  {
    rem := Sub(rem, divisor);
    ghost remVal := Str2Int(rem);
    q := Add(q, "1");
    ghost qVal := Str2Int(q);
  }
  quotient := q;
  remainder := rem;
}
// </vc-code>

