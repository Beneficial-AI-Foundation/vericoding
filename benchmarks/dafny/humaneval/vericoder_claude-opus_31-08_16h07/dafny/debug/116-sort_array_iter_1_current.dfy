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
    invariant multiset(sorted) <= multiset(s)
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
    
    // Insert current at position j
    sorted := sorted[..j] + [current] + sorted[j..];
    
    // Prove that multiset is preserved
    assert s[..i+1] == s[..i] + [s[i]];
    assert current == s[i];
    InsertPreservesMultiset(current, sorted[..|sorted|-1], j);
    
    i := i + 1;
  }
  
  assert s[..|s|] == s;
}
// </vc-code>

