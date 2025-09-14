// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Contains(s: array<int>, val: int, start: int, end: int): bool
{
  if start >= end then false else
  if s[start] == val then true else
  Contains(s, val, start + 1, end)
}
/* helper modified by LLM (iteration 5): added Contains helper to search for value in sorted array */
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
{
  /* code modified by LLM (iteration 5): removed trigger syntax from for loop to fix compilation error */
  v := 0;
  for i := 0 to s.Length-1
    invariant 0 <= v <= s.Length + 1
    invariant forall k :: 0 <= k < v ==> Contains(s, k, 0, i)
  {
    if s[i] > v {
      break;
    } else if s[i] == v {
      v := v + 1;
    }
  }
}
// </vc-code>
