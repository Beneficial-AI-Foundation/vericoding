//IMPL SequenceConcat
lemma SequenceConcat(s:seq<int>, pivot:int)
 requires 0<=pivot<|s|
 ensures s[..pivot] + s[pivot..] == s
{
  // This is a built-in property of sequence slicing in Dafny
  // The lemma body can be empty as Dafny can prove this automatically
}

predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate Multiset(s1: seq<int>, s2: seq<int>)
{
  multiset(s1) == multiset(s2)
}

predicate SortSpec(input: seq<int>, output: seq<int>)
{
  Sorted(output) && Multiset(input, output)
}

/* code modified by LLM (iteration 4): Added helper lemma to prove multiset property for sequence concatenation */
lemma MultisetConcat(s: seq<int>, pivot: int)
  requires 0 <= pivot < |s|
  ensures multiset(s) == multiset(s[..pivot]) + multiset(s[pivot..])
{
  // Dafny can prove this automatically
}

/* code modified by LLM (iteration 4): Added helper lemma for sorted sequence properties */
lemma SortedSlice(s: seq<int>, i: int, j: int)
  requires Sorted(s)
  requires 0 <= i <= j <= |s|
  ensures Sorted(s[i..j])
{
  // Dafny can prove this automatically
}

method merge_sort(input:seq<int>) returns (output:seq<int>)
 ensures SortSpec(input, output)
{
  if |input| <= 1 {
    output := input;
  } else {
    var mid := |input| / 2;
    /* code modified by LLM (iteration 4): Added sequence concatenation lemma call */
    SequenceConcat(input, mid);
    MultisetConcat(input, mid);
    var left := merge_sort(input[..mid]);
    var right := merge_sort(input[mid..]);
    output := merge(left, right);
    /* code modified by LLM (iteration 4): Added explicit multiset reasoning with transitive property */
    assert multiset(output) == multiset(left) + multiset(right);
    assert multiset(left) == multiset(input[..mid]);
    assert multiset(right) == multiset(input[mid..]);
    assert multiset(input[..mid]) + multiset(input[mid..]) == multiset(input);
    assert multiset(output) == multiset(input);
  }
}

method merge(left: seq<int>, right: seq<int>) returns (result: seq<int>)
  requires Sorted(left) && Sorted(right)
  ensures Sorted(result)
  ensures multiset(result) == multiset(left) + multiset(right)
{
  result := [];
  var i, j := 0, 0;
  
  while i < |left| || j < |right|
    invariant 0 <= i <= |left| && 0 <= j <= |right|
    invariant Sorted(result)
    invariant multiset(result) == multiset(left[..i]) + multiset(right[..j])
    /* code modified by LLM (iteration 4): Added invariants to maintain sorted property during merge */
    invariant forall k :: 0 <= k < |result| ==> 
      (i < |left| ==> result[k] <= left[i]) &&
      (j < |right| ==> result[k] <= right[j])
    invariant i < |left| && j < |right| ==> left[i] <= right[j] || right[j] <= left[i]
  {
    if i >= |left| {
      /* code modified by LLM (iteration 4): Added assertion to help with sorted property */
      assert j < |right|;
      result := result + [right[j]];
      j := j + 1;
    } else if j >= |right| {
      assert i < |left|;
      result := result + [left[i]];
      i := i + 1;
    } else if left[i] <= right[j] {
      /* code modified by LLM (iteration 4): Added assertions to maintain sorted property */
      assert Sorted(result + [left[i]]);
      result := result + [left[i]];
      i := i + 1;
    } else {
      assert right[j] < left[i];
      assert Sorted(result + [right[j]]);
      result := result + [right[j]];
      j := j + 1;
    }
  }
  
  /* code modified by LLM (iteration 4): Final assertions to complete the proof */
  assert i == |left| && j == |right|;
  assert left[..i] == left && right[..j] == right;
  assert multiset(result) == multiset(left) + multiset(right);
}