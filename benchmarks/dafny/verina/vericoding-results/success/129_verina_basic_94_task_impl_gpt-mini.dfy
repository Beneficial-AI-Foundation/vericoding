// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): adds reads clauses for arrays */
predicate PrefixCopied(s: array<int>, r: array<int>, i: int) reads s, r { 0 <= i <= s.Length && r.Length == s.Length && forall j :: 0 <= j < i ==> r[j] == s[j] }
// </vc-helpers>

// <vc-spec>
method IterCopy(s: array<int>) returns (result: array<int>)
    ensures
        s.Length == result.Length &&
        forall i :: 0 <= i < s.Length ==> s[i] == result[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterative copy with loop invariants */
  result := new int[s.Length];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant result.Length == s.Length
    invariant forall j :: 0 <= j < i ==> result[j] == s[j]
  {
    result[i] := s[i];
    i := i + 1;
  }
}
// </vc-code>
