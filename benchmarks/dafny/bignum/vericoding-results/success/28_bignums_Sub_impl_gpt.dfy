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
function Int2Str(n: nat): string
  decreases n
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 then
    ""
  else
    Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

function Eval(s: string): nat
  decreases s
{
  if |s| == 0 then  0  else  (2 * Eval(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

lemma ValidBitStringPrefix(s: string, k: nat)
  requires k <= |s|
  requires ValidBitString(s)
  ensures ValidBitString(s[0..k])
{
  assert forall i :: 0 <= i < k ==> s[i] == '0' || s[i] == '1';
}

lemma EvalEqStr2Int(s: string)
  requires ValidBitString(s)
  ensures Eval(s) == Str2Int(s)
  decreases s
{
  if |s| != 0 {
    ValidBitStringPrefix(s, |s|-1);
    EvalEqStr2Int(s[0..|s|-1]);
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
  EvalEqStr2Int(s1);
  EvalEqStr2Int(s2);
  var n1 := Eval(s1);
  var n2 := Eval(s2);
  assert n1 >= n2;
  return Int2Str((n1 - n2) as nat);
}
// </vc-code>

