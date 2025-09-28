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
/* helper modified by LLM (iteration 6): replaced Str2IntProps with a lemma about appending a character */
lemma lemma_Str2Int_append(s: string, c: char)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures ValidBitString(s + [c])
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
}

/* helper modified by LLM (iteration 6): rewrote Str2Nat to use new lemma and fix postcondition proof */
method Str2Nat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
    decreases |s| - i
  {
    assert s[0..i+1] == s[0..i] + [s[i]];
    lemma_Str2Int_append(s[0..i], s[i]);
    var digit := if s[i] == '1' then 1 else 0;
    n := 2 * n + digit;
    i := i + 1;
  }
  assert s[0..|s|] == s;
}

function Int2Str(n: nat): (res: string)
  ensures ValidBitString(res)
  ensures Str2Int(res) == n
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else
    Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
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
  /* code modified by LLM (iteration 6): no changes needed, logic relies on helpers */
  var n1: nat;
  n1 := Str2Nat(s1);
  var n2: nat;
  n2 := Str2Nat(s2);
  var n_res := n1 * n2;
  res := Int2Str(n_res);
}
// </vc-code>
