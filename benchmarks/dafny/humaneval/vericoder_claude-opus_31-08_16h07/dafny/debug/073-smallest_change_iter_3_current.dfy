

// <vc-helpers>
lemma SetCardinalityHelper(s: seq<int>, k: int, currSet: set<int>)
  requires 0 <= k <= |s| / 2
  requires currSet == set i | 0 <= i < k && s[i] != s[|s| - 1 - i]
  ensures |currSet| <= k
{
  if k == 0 {
    assert currSet == {};
  } else {
    var prevSet := set i | 0 <= i < k - 1 && s[i] != s[|s| - 1 - i];
    SetCardinalityHelper(s, k - 1, prevSet);
    
    if s[k - 1] != s[|s| - 1 - (k - 1)] {
      assert currSet == prevSet + {k - 1};
    } else {
      assert currSet == prevSet;
    }
  }
}

lemma SetEquality(s: seq<int>, k: int, currSet: set<int>, targetSet: set<int>)
  requires 0 <= k <= |s| / 2
  requires currSet == set i | 0 <= i < k && s[i] != s[|s| - 1 - i]
  requires targetSet == set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]
  requires forall i :: k <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
  ensures currSet == targetSet
{
  forall x | x in targetSet
    ensures x in currSet
  {
    assert x < k;
  }
  
  forall x | x in currSet
    ensures x in targetSet
  {
    assert x < |s| / 2;
  }
}

lemma SetUpdateLemma(s: seq<int>, k: int, prevSet: set<int>, currSet: set<int>)
  requires 0 <= k < |s| / 2
  requires prevSet == set i | 0 <= i < k && s[i] != s[|s| - 1 - i]
  requires currSet == set i | 0 <= i < k + 1 && s[i] != s[|s| - 1 - i]
  ensures s[k] != s[|s| - 1 - k] ==> currSet == prevSet + {k} && |currSet| == |prevSet| + 1
  ensures s[k] == s[|s| - 1 - k] ==> currSet == prevSet && |currSet| == |prevSet|
{
  if s[k] != s[|s| - 1 - k] {
    assert k in currSet;
    assert k !in prevSet;
    assert currSet == prevSet + {k};
  } else {
    assert k !in currSet;
    assert currSet == prevSet;
  }
}
// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)
  // post-conditions-start
  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  c := 0;
  ghost var currSet := set i | 0 <= i < 0 && s[i] != s[|s| - 1 - i];
  assert currSet == {};
  
  var k := 0;
  while k < |s| / 2
    invariant 0 <= k <= |s| / 2
    invariant currSet == set i | 0 <= i < k && s[i] != s[|s| - 1 - i]
    invariant c == |currSet|
  {
    ghost var prevSet := currSet;
    if s[k] != s[|s| - 1 - k] {
      c := c + 1;
    }
    k := k + 1;
    currSet := set i | 0 <= i < k && s[i] != s[|s| - 1 - i];
    SetUpdateLemma(s, k - 1, prevSet, currSet);
  }
  
  assert currSet == set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i];
}
// </vc-code>

