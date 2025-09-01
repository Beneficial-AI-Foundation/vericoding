

// <vc-helpers>
lemma SetCardinalityLemma(s: seq<int>)
  ensures |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]| <= |s| / 2
{
  var setOfIndices := set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i];
  var allIndices := set i | 0 <= i < |s| / 2;
  assert setOfIndices <= allIndices;
  
  // Prove cardinality of allIndices equals |s| / 2
  if |s| >= 2 {
    // Show bijection between allIndices and range [0, |s|/2)
    assert forall k :: 0 <= k < |s| / 2 ==> k in allIndices;
    assert forall k :: k in allIndices ==> 0 <= k < |s| / 2;
    // Use the fact that allIndices contains exactly the integers from 0 to |s|/2 - 1
    assert allIndices == set k | 0 <= k < |s| / 2;
  }
  
  // The cardinality follows from the range
  CardinalityOfRange(|s| / 2);
  assert |allIndices| == |s| / 2;
  assert |setOfIndices| <= |allIndices|;
}

lemma CardinalityOfRange(n: nat)
  ensures |set i | 0 <= i < n| == n
{
  if n == 0 {
    var emptySet: set<int> := {};
    assert (set i | 0 <= i < 0) == emptySet;
  } else {
    var s := set i | 0 <= i < n;
    var prev := set i | 0 <= i < n - 1;
    assert s == prev + {n - 1};
    CardinalityOfRange(n - 1);
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
  var i := 0;
  var targetSet := set j | 0 <= j < |s| / 2 && s[j] != s[|s| - 1 - j];
  var processedSet := {};
  
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant processedSet == set j | 0 <= j < i && s[j] != s[|s| - 1 - j]
    invariant c == |processedSet|
    invariant targetSet == set j | 0 <= j < |s| / 2 && s[j] != s[|s| - 1 - j]
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

