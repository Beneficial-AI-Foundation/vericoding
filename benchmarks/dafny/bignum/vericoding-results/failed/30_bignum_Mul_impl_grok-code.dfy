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

// <vc-helpers>
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases |s|
{
  if |s| == 0 then 0 else 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "0" else if n % 2 == 0 then Int2Str(n / 2) + "0" else Int2Str(n / 2) + "1"
}

lemma Int2StrValid(n: nat)
  ensures ValidBitString(Int2Str(n))
{
  if n > 0 {
    Int2StrValid(n / 2);
  }
}

lemma Int2StrRoundTrip(n: nat)
  ensures Str2Int(Int2Str(n)) == n
{
  if n > 0 {
    Int2StrRoundTrip(n / 2);
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
  var mul := Str2Int(s1) * Str2Int(s2);
  res := Int2Str(mul);
}
// </vc-code>

