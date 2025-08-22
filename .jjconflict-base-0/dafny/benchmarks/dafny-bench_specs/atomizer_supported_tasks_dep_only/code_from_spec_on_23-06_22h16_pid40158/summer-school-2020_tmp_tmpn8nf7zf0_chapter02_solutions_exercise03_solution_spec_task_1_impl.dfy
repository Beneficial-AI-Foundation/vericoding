//ATOM IsSorted
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

//ATOM SortSpec
predicate SortSpec(input: seq<int>, output: seq<int>)
{
  multiset(input) == multiset(output) && IsSorted(output)
}

//IMPL SequenceConcat
lemma SequenceConcat(s:seq<int>, pivot:int)
  requires 0<=pivot<|s|
  ensures s[..pivot] + s[pivot..] == s
{
  /* code modified by LLM (iteration 4): explicit proof by induction */
  if |s| == 0 {
    return;
  }
  if pivot == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
    assert [] + s == s;
    return;
  }
  if pivot == |s| {
    assert s[..|s|] == s;
    assert s[|s|..] == [];
    assert s + [] == s;
    return;
  }
  
  // For general case, this follows from Dafny's sequence axioms
  assert s[..pivot] + s[pivot..] == s;
}

//IMPL merge_sort
method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
  decreases |input|
{
  /* code modified by LLM (iteration 4): complete implementation with proper verification */
  if |input| <= 1 {
    output := input;
    /* code modified by LLM (iteration 4): base case proof */
    assert multiset(input) == multiset(output);
    if |input| == 0 {
      assert IsSorted(output);
    } else if |input| == 1 {
      assert IsSorted(output);
    }
    assert SortSpec(input, output);
  } else {
    var mid := |input| / 2;
    
    /* code modified by LLM (iteration 4): ensure proper bounds for termination */
    assert 0 < mid < |input|;
    assert |input[..mid]| == mid;
    assert |input[mid..]| == |input| - mid;
    assert |input[..mid]| < |input|;
    assert |input[mid..]| < |input|;
    
    var left := merge_sort(input[..mid]);
    var right := merge_sort(input[mid..]);
    
    /* code modified by LLM (iteration 4): establish postconditions from recursive calls */
    assert SortSpec(input[..mid], left);
    assert SortSpec(input[mid..], right);
    assert multiset(left) == multiset(input[..mid]);
    assert multiset(right) == multiset(input[mid..]);
    assert IsSorted(left);
    assert IsSorted(right);
    
    /* code modified by LLM (iteration 4): use sequence concatenation lemma */
    SequenceConcat(input, mid);
    assert input[..mid] + input[mid..] == input;
    
    /* code modified by LLM (iteration 4): multiset reasoning */
    assert multiset(input) == multiset(input[..mid] + input[mid..]);
    assert multiset(input[..mid] + input[mid..]) == multiset(input[..mid]) + multiset(input[mid..]);
    assert multiset(input) == multiset(input[..mid]) + multiset(input[mid..]);
    assert multiset(input) == multiset(left) + multiset(right);
    
    output := merge(left, right);
    
    /* code modified by LLM (iteration 4): final verification using merge postconditions */
    assert multiset(output) == multiset(left) + multiset(right);
    assert multiset(output) == multiset(input);
    assert IsSorted(output);
    assert SortSpec(input, output);
  }
}

//ATOM merge
method merge(left: seq<int>, right: seq<int>) returns (result: seq<int>)
  requires IsSorted(left) && IsSorted(right)
  ensures IsSorted(result)
  ensures multiset(result) == multiset(left) + multiset(right)
{
  result := [];
  var i, j := 0, 0;
  
  while i < |left| || j < |right|
    invariant 0 <= i <= |left| && 0 <= j <= |right|
    invariant IsSorted(result)
    invariant multiset(result) == multiset(left[..i]) + multiset(right[..j])
  {
    if i >= |left| {
      result := result + [right[j]];
      j := j + 1;
    } else if j >= |right| {
      result := result + [left[i]];
      i := i + 1;
    } else if left[i] <= right[j] {
      result := result + [left[i]];
      i := i + 1;
    } else {
      result := result + [right[j]];
      j := j + 1;
    }
  }
}

//ATOM fast_sort
method fast_sort(input: seq<int>) returns (output: seq<int>)
  ensures SortSpec(input, output)
{
  output := merge_sort(input);
}