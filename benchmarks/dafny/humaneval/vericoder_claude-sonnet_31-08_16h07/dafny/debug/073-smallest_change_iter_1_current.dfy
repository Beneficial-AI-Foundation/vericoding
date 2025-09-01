

// <vc-helpers>
lemma SetCardinalityLemma(s: seq<int>)
  ensures |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]| <= |s| / 2
{
  var setOfIndices := set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i];
  var allIndices := set i | 0 <= i < |s| / 2;
  assert setOfIndices <= allIndices;
  assert |allIndices| == |s| / 2;
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
  var i := 0;
  var targetSet := set j | 0 <= j < |s| / 2 && s[j] != s[|s| - 1 - j];
  var processedSet := {};
  
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant processedSet == set j | 0 <= j < i && s[j] != s[|s| - 1 - j]
    invariant c == |processedSet|
  {
    if s[i] != s[|s| - 1 - i] {
      processedSet := processedSet + {i};
      c := c + 1;
    }
    i := i + 1;
  }
  
  assert processedSet == targetSet;
}
// </vc-code>

