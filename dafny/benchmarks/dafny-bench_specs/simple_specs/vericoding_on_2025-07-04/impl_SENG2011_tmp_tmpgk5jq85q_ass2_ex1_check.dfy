//ATOM
// method verifies
method StringSwap(s: string, i:nat, j:nat) returns (t: string)
requires i >= 0 && j >= 0 && |s| >= 0
requires |s| > 0 ==> i < |s| && j < |s|
ensures multiset(s[..]) == multiset(t[..])
ensures |s| == |t|
ensures |s| > 0 ==> forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k]
ensures |s| > 0 ==> t[i] == s[j] && t[j] == s[i]
ensures |s| == 0 ==> t == s
{
  if |s| == 0 {
    t := s;
  } else {
    /* code modified by LLM (iteration 1): Fixed sequence construction to properly swap characters */
    var chars := seq(|s|, k => if k == i then s[j] else if k == j then s[i] else s[k]);
    t := chars;
    
    /* code modified by LLM (iteration 1): Added assertions to help verification */
    assert |t| == |s|;
    assert forall k :: 0 <= k < |s| && k != i && k != j ==> t[k] == s[k];
    assert t[i] == s[j] && t[j] == s[i];
  }
}

//IMPL SPEC
/* code modified by LLM (iteration 1): Provided minimal implementation for empty method */
method check() {
}