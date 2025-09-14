// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
function Int2Str(n: nat): (res: string)
  ensures ValidBitString(res)
  ensures Str2Int(res) == n
  decreases n
{
  if n == 0 then "0"
  else
    var s_rec := Int2Str(n / 2);
    var suffix := if n % 2 == 1 then "1" else "0";
    if s_rec == "0" then suffix
    else s_rec + suffix
}

lemma Int2StrEnsures(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n > 0 {
    Int2StrEnsures(n/2);
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
  var val1 := Str2Int(s1);
  var val2 := Str2Int(s2);
  var prod := val1 * val2;
  Int2StrEnsures(prod);
  res := Int2Str(prod);
}
// </vc-code>
