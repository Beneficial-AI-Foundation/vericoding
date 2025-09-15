// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added function and lemma to reason about difference count */
function CountDifferences(s: seq<int>, limit: int): nat
  requires 0 <= limit <= |s| / 2
{
  |set i | 0 <= i < limit && s[i] != s[|s| - 1 - i]|
}

lemma CountDifferencesRecursive(s: seq<int>, k: int)
  requires 0 <= k < |s| / 2
  ensures CountDifferences(s, k + 1) == CountDifferences(s, k) + (if s[k] != s[|s| - 1 - k] then 1 else 0)
{
}
// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)

  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): used helper function and lemma to prove loop invariant */
  c := 0;
  var i := 0;
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant c == CountDifferences(s, i)
  {
    CountDifferencesRecursive(s, i);
    if s[i] != s[|s| - 1 - i] {
      c := c + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
