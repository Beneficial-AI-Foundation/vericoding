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
function StrToNat(s: string): nat
  requires ValidBitString(s)
  decreases s
  ensures StrToNat(s) == Str2Int(s)
{
  if |s| == 0 then 0 else 2 * StrToNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function IntToStr(n: nat): string
  decreases n
  ensures ValidBitString(IntToStr(n))
  ensures Str2Int(IntToStr(n)) == n
{
  if n == 0 then "" else IntToStr(n / 2) + (if n % 2 == 1 then "1" else "0")
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
  var n1 := StrToNat(s1);
  var n2 := StrToNat(s2);
  var d := n1 - n2;
  res := IntToStr(d);
}
// </vc-code>

