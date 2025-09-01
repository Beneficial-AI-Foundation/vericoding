function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
lemma PopcountNonnegative(n: nat)
  ensures popcount(n) >= 0
{
}

lemma InsertPreservesMultiset(x: nat, s: seq<nat>, i: nat)
  requires 0 <= i <= |s|
  ensures multiset(s[..i] + [x] + s[i..]) == multiset([x]) + multiset(s)
{
  assert s == s[..i] + s[i..];
  assert s[..i] + [x] + s[i..] == s[..i] + ([x] + s[i..]);
}

lemma MultisetSliceNext(s: seq<nat>, i: nat)
  requires 0 <= i < |s|
  ensures multiset(s[..i+1]) == multiset(s[..i]) + multiset([s[i]])
{
  assert s[..i+1] == s[..i] + [s[i]];
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := [];
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant forall j, k :: 0 <= j < k < |sorted| ==> popcount(sorted[j]) <= popcount(sorted[k])
    invariant multiset(sorted) == multiset(s[..i])
  {
    var current := s[i];
    var j := 0;
    
    // Find insertion position
    while j < |sorted| && popcount(sorted[j]) <= popcount(current)
      invariant 0 <= j <= |sorted|
      invariant forall k :: 0 <= k < j ==> popcount(sorted[k]) <= popcount(current)
    {
      j := j + 1;
    }
    
    // Store old sorted for reasoning
    var oldSorted := sorted;
    
    // Insert current at position j
    sorted := sorted[..j] + [current] + sorted[j..];
    
    // Prove that multiset is preserved
    assert oldSorted == oldSorted[..j] + oldSorted[j..];
    assert sorted == oldSorted[..j] + [current] + oldSorted[j..];
    assert multiset(sorted) == multiset(oldSorted[..j]) + multiset([current]) + multiset(oldSorted[j..]);
    assert multiset(sorted) == multiset(oldSorted) + multiset([current]);
    assert multiset(oldSorted) == multiset(s[..i]);
    assert current == s[i];
    MultisetSliceNext(s, i);
    assert multiset(s[..i+1]) == multiset(s[..i]) + multiset([s[i]]);
    assert multiset(sorted) == multiset(s[..i]) + multiset([current]);
    assert multiset(sorted) == multiset(s[..i+1]);
    
    i := i + 1;
  }
  
  assert i == |s|;
  assert s[..|s|] == s;
  assert multiset(sorted) == multiset(s[..|s|]);
}
// </vc-code>

