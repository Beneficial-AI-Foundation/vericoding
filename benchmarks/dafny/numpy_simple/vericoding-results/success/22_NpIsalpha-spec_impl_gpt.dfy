// <vc-preamble>
predicate IsAlphaChar(c: char)
{
    ('A' <= c <= 'Z') || ('a' <= c <= 'z')
}

predicate StringIsAlpha(s: seq<char>)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> IsAlphaChar(s[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Provide a predicate-style function to express that the first k characters are alphabetic */
function AllAlphaPrefix(s: seq<char>, k: int): bool
  requires 0 <= k <= |s|
{
  forall t :: 0 <= t < k ==> IsAlphaChar(s[t])
}
// </vc-helpers>

// <vc-spec>
method IsAlpha(input: array<string>) returns (ret: array<bool>)
    ensures
        ret.Length == input.Length &&
        forall i :: 0 <= i < input.Length ==> 
            ret[i] == StringIsAlpha(input[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Implement loop to compute per-string isalpha without null comparisons */
  var n := input.Length;
  ret := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant ret.Length == n
    invariant forall j :: 0 <= j < i ==> ret[j] == StringIsAlpha(input[j])
  {
    var s := input[i];
    var k := 0;
    var allAlpha := true;
    while k < |s|
      invariant 0 <= k <= |s|
      invariant allAlpha == (forall t :: 0 <= t < k ==> IsAlphaChar(s[t]))
    {
      allAlpha := allAlpha && IsAlphaChar(s[k]);
      k := k + 1;
    }
    ret[i] := |s| > 0 && allAlpha;
    i := i + 1;
  }
}
// </vc-code>
