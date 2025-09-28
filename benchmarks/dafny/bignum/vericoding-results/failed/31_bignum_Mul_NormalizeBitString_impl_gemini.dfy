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

method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 7): [fixed lemma proof body to be empty to allow automatic proof by unfolding] */
lemma Str2IntAppend(s: string, c: char)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
}

/* helper modified by LLM (iteration 4): [added ValidBitString invariant to help verifier] */
method ToInt(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant ValidBitString(s[..i])
    invariant n == Str2Int(s[..i])
  {
    Str2IntAppend(s[..i], s[i]);
    n := 2 * n + (if s[i] == '1' then 1 else 0);
    i := i + 1;
  }
}

/* helper modified by LLM (iteration 4): [added lemma call to prove postcondition] */
method FromInt(n_in: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n_in
  ensures |s| > 0
  ensures |s| > 1 ==> s[0] != '0'
  decreases n_in
{
  if n_in == 0 {
    s := "0";
  } else {
    if (n_in == 1) {
      s := "1";
    } else {
      var rest := FromInt(n_in / 2);
      var bit := if n_in % 2 == 1 then "1" else "0";
      Str2IntAppend(rest, bit[0]);
      s := rest + bit;
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
  /* code modified by LLM (iteration 7): [no change to logic, helpers fixed] */
  var n1 := ToInt(s1);
  var n2 := ToInt(s2);
  var prod := n1 * n2;
  res := FromInt(prod);
}
// </vc-code>
