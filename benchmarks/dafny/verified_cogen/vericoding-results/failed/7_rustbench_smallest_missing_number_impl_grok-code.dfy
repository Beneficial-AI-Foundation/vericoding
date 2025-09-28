// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes, keep empty */
// </vc-helpers>

// <vc-spec>
method SmallestMissingNumber(s: array<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < s.Length ==> s[i] <= s[j]
    requires forall i :: 0 <= i < s.Length ==> s[i] >= 0
    requires s.Length <= 100_000
    ensures 0 <= v
    ensures forall i :: 0 <= i < s.Length ==> s[i] != v
    ensures forall k {:trigger} :: 0 <= k < v ==> exists j :: 0 <= j < s.Length && s[j] == k
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added {:trigger} to the quantifier in loop invariant to help verification */
{
  v := 0;
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant 0 <= v
    invariant forall j :: 0 <= j < i ==> s[j] != v
    invariant forall k {:trigger} :: 0 <= k < v ==> exists j :: 0 <= j < i && s[j] == k
  {
    if s[i] == v {
      v := v + 1;
      i := i + 1;
    } else if s[i] > v {
      break;
    } else {
      i := i + 1;
    }
  }
}
// </vc-code>
