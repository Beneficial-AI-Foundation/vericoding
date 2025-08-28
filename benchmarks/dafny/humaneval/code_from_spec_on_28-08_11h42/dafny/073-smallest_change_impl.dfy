// <vc-helpers>
lemma SetCardinalityLemma(s: seq<int>, i: int)
  requires 0 <= i < |s| / 2
  requires s[i] != s[|s| - 1 - i]
  ensures (set j | 0 <= j < i + 1 && s[j] != s[|s| - 1 - j]) == 
          (set j | 0 <= j < i && s[j] != s[|s| - 1 - j]) + {i}
{
  var oldSet := set j | 0 <= j < i && s[j] != s[|s| - 1 - j];
  var newSet := set j | 0 <= j < i + 1 && s[j] != s[|s| - 1 - j];
  
  assert i in newSet;
  assert i !in oldSet;
  
  forall j | j in newSet
    ensures j in oldSet || j == i
  {
    if j != i {
      assert 0 <= j < i;
      assert j in oldSet;
    }
  }
  
  forall j | j in oldSet
    ensures j in newSet
  {
    assert 0 <= j < i < i + 1;
    assert j in newSet;
  }
}

lemma SetCardinalityLemmaNoChange(s: seq<int>, i: int)
  requires 0 <= i < |s| / 2
  requires s[i] == s[|s| - 1 - i]
  ensures (set j | 0 <= j < i + 1 && s[j] != s[|s| - 1 - j]) == 
          (set j | 0 <= j < i && s[j] != s[|s| - 1 - j])
{
  var oldSet := set j | 0 <= j < i && s[j] != s[|s| - 1 - j];
  var newSet := set j | 0 <= j < i + 1 && s[j] != s[|s| - 1 - j];
  
  assert i !in newSet;
  assert i !in oldSet;
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
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant c == |set j | 0 <= j < i && s[j] != s[|s| - 1 - j]|
  {
    if s[i] != s[|s| - 1 - i] {
      SetCardinalityLemma(s, i);
      c := c + 1;
    } else {
      SetCardinalityLemmaNoChange(s, i);
    }
    i := i + 1;
  }
}
// </vc-code>
