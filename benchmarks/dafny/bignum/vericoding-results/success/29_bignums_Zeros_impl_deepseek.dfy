predicate AllZero(s: string)
{
  |s| == 0 || forall i | 0 <= i < |s| :: s[i] == '0'
}
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

// <vc-helpers>
lemma AllZeroConcat(s: string, c: char)
  requires AllZero(s) && (c == '0')
  ensures AllZero(s + [c])
{
}

lemma Str2IntZero(s: string)
  requires AllZero(s)
  ensures Str2Int(s) == 0
{
}
// </vc-helpers>

// <vc-spec>
method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    s := "";
  } else {
    var t := Zeros(n - 1);
    s := t + "0";
  }
}
// </vc-code>

