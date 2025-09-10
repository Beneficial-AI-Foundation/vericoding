function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
lemma digit_sum_stable(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures digits_sum(s[i]) == digits_sum(s[i])
  ensures digits_sum(s[j]) == digits_sum(s[j])
{
}

predicate sorted_by_digit_sum(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> digits_sum(s[i]) <= digits_sum(s[j])
}

lemma insert_preserves_multiset(s: seq<int>, x: int, pos: int)
  requires 0 <= pos <= |s|
  ensures multiset(s[..pos] + [x] + s[pos..]) == multiset(s) + multiset{x}
{
  // Need to prove that splitting and reconstructing preserves multiset
  assert s == s[..pos] + s[pos..];
  assert multiset(s[..pos] + [x] + s[pos..]) 
      == multiset(s[..pos]) + multiset{x} + multiset(s[pos..])
      == multiset(s[..pos]) + multiset(s[pos..]) + multiset{x}
      == multiset(s[..pos] + s[pos..]) + multiset{x}
      == multiset(s) + multiset{x};
}

lemma sorted_prefix_property(s: seq<int>, i: int)
  requires 0 < i <= |s|
  requires sorted_by_digit_sum(s[..i])
  ensures forall j, k :: 0 <= j < k < i ==> digits_sum(s[j]) <= digits_sum(s[k])
{
}
// </vc-helpers>

// <vc-spec>
method order_by_points(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
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
    invariant sorted_by_digit_sum(sorted)
    invariant multiset(sorted) + multiset(s[i..]) == multiset(s)
  {
    var current := s[i];
    var j := 0;
    
    // Find insertion position
    while j < |sorted| && digits_sum(sorted[j]) <= digits_sum(current)
      invariant 0 <= j <= |sorted|
      invariant forall k :: 0 <= k < j ==> digits_sum(sorted[k]) <= digits_sum(current)
    {
      j := j + 1;
    }
    
    // Store the old sorted sequence for reasoning
    var oldSorted := sorted;
    
    // Insert current at position j
    sorted := sorted[..j] + [current] + sorted[j..];
    
    // Apply the lemma to prove multiset preservation
    insert_preserves_multiset(oldSorted, current, j);
    assert multiset(sorted) == multiset(oldSorted) + multiset{current};
    
    // Prove that sorted remains sorted
    assert sorted_by_digit_sum(sorted);
    
    i := i + 1;
  }
}
// </vc-code>

