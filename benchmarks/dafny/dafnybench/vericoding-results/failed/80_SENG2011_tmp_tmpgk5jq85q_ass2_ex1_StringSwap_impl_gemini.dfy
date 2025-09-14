// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Resubmitting correct helper function. */
function swap<T>(s: seq<T>, i: nat, j: nat): (r: seq<T>)
  requires i < |s| && j < |s|
  ensures |r| == |s|
  ensures multiset(r[..]) == multiset(s[..])
  ensures r[i] == s[j] && r[j] == s[i]
  ensures forall k :: 0 <= k < |s| && k != i && k != j ==> r[k] == s[k]
{
  s[i := s[j]][j := s[i]]
}
// </vc-helpers>

// <vc-spec>
method StringSwap(s: string, i:nat, j:nat) returns (t: string)
requires i >= 0 && j >= 0 && |s| >= 0;
requires |s| > 0 ==> i < |s| && j < |s|;
ensures multiset(s[..]) == multiset(t[..]);
ensures |s| == |t|;
ensures |s| > 0 ==> forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k]
ensures |s| > 0 ==> t[i] == s[j] && t[j] == s[i];
ensures |s| == 0 ==> t == s;
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Simplified logic by removing redundant i==j check. */
  if |s| == 0 {
    t := s;
  } else {
    t := swap(s, i, j);
  }
}
// </vc-code>
