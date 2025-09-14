// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): checks if value is contained in seq */
function Contains(s: seq<int>, x: int): bool { exists j :: 0 <= j < |s| && s[j] == x }
// </vc-helpers>

// <vc-spec>
method SetToSeq(s: seq<int>) returns (result: seq<int>)
    ensures
        // All elements are unique in the result  
        forall i: int, j: int :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures
        // Every element in result is in s
        forall i: int :: 0 <= i < |result| ==> 
            exists j: int :: 0 <= j < |s| && s[j] == result[i]
    ensures
        // Every element in s is in result
        forall i: int :: 0 <= i < |s| ==> 
            exists j: int :: 0 <= j < |result| && result[j] == s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build sequence of unique elements preserving order with explicit invariants and proofs */
  var i := 0;
  result := [];
  var n := |s|;
  while i < n
    invariant 0 <= i <= n
    invariant forall a, b :: 0 <= a < b < |result| ==> result[a] != result[b]
    invariant forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < i && s[j] == result[k]
    invariant forall j :: 0 <= j < i ==> exists k :: 0 <= k < |result| && result[k] == s[j]
  {
    var prev := result;
    var prevLen := |prev|;
    // Use snapshot facts about prev captured from invariants at loop head
    assert forall a, b :: 0 <= a < b < prevLen ==> prev[a] != prev[b];
    assert forall k :: 0 <= k < prevLen ==> exists j :: 0 <= j < i && s[j] == prev[k];
    assert forall j :: 0 <= j < i ==> exists k :: 0 <= k < prevLen && prev[k] == s[j];

    var x := s[i];
    var had := exists k :: 0 <= k < prevLen && prev[k] == x;
    if !had {
      result := prev + [x];
      assert |result| == prevLen + 1;
      // prefix elements unchanged
      assert forall k :: 0 <= k < prevLen ==> result[k] == prev[k];
      // appended element equals x
      assert result[prevLen] == x;
      // uniqueness: prev unique and x not in prev
      assert forall a, b :: 0 <= a < b < |result| ==> result[a] != result[b];
    } else {
      result := prev;
      assert |result| == prevLen;
      // previous facts about prev still hold and imply the relaxed facts for i+1
      assert forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < i && s[j] == result[k];
      // s[i] already has a representative in result because had
      assert exists k :: 0 <= k < |result| && result[k] == s[i];
      assert forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < i+1 && s[j] == result[k];
    }

    // Now show every element of result comes from s[0..i]
    if !had {
      // old elements come from prev (j < i)
      assert forall k :: 0 <= k < prevLen ==> exists j :: 0 <= j < i && s[j] == result[k];
      // appended element comes from s[i]
      assert exists j :: 0 <= j < i+1 && s[j] == result[prevLen];
      assert forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < i+1 && s[j] == result[k];
    } else {
      // already established above for else-branch
      assert forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < i+1 && s[j] == result[k];
    }

    // Show every processed s[j] for j < i+1 has representation in result
    if !had {
      assert forall j :: 0 <= j < i ==> exists k :: 0 <= k < |result| && result[k] == s[j];
      // s[i] is represented by appended element
      assert exists k :: 0 <= k < |result| && result[k] == s[i];
      assert forall j :: 0 <= j < i+1 ==> exists k :: 0 <= k < |result| && result[k] == s[j];
    } else {
      // had implies s[i] already had representation
      assert forall j :: 0 <= j < i+1 ==> exists k :: 0 <= k < |result| && result[k] == s[j];
    }

    i := i + 1;
  }
  // Final assertions matching the method postconditions
  assert forall a, b :: 0 <= a < b < |result| ==> result[a] != result[b];
  assert forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < n && s[j] == result[k];
  assert forall j :: 0 <= j < n ==> exists k :: 0 <= k < |result| && result[k] == s[j];
}

// </vc-code>
