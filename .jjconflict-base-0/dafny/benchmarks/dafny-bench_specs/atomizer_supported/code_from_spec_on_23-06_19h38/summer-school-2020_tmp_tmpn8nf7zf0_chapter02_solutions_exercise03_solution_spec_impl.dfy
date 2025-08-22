// ATOM 
predicate IsSorted(s:seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

// ATOM 
predicate SortSpec(input:seq<int>, output:seq<int>)
{
  && IsSorted(output)
  && multiset(output) == multiset(input)
}

//IMPL SequenceConcat
lemma SequenceConcat(s:seq<int>, pivot:int)
  requires 0<=pivot<|s|
  ensures s[..pivot] + s[pivot..] == s
{
  /* code modified by LLM (iteration 4): added proof body for sequence concatenation */
  // This is a built-in property of sequence slicing in Dafny
}

//IMPL merge_sort
method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
  decreases |input|
{
  if |input| <= 1 {
    return input;
  }
  
  var mid := |input| / 2;
  /* code modified by LLM (iteration 4): added assertion to help with sequence concatenation */
  assert input[..mid] + input[mid..] == input;
  var left := merge_sort(input[..mid]);
  var right := merge_sort(input[mid..]);
  output := merge(left, right);
  /* code modified by LLM (iteration 4): added assertions to help verify the final postcondition */
  assert multiset(output) == multiset(left + right);
  assert multiset(left + right) == multiset(input[..mid] + input[mid..]);
  assert multiset(input[..mid] + input[mid..]) == multiset(input);
}

//IMPL merge
method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures SortSpec(a+b, output)
{
  var i, j := 0, 0;
  output := [];
  
  while i < |a| || j < |b|
    invariant 0 <= i <= |a|
    invariant 0 <= j <= |b|
    invariant IsSorted(output)
    invariant multiset(output) == multiset(a[..i]) + multiset(b[..j])
    /* code modified by LLM (iteration 4): improved invariants for merge correctness */
    invariant i < |a| && j < |b| ==> (|output| == 0 || (output[|output|-1] <= a[i] && output[|output|-1] <= b[j]))
    invariant i < |a| && j >= |b| ==> (|output| == 0 || output[|output|-1] <= a[i])
    invariant i >= |a| && j < |b| ==> (|output| == 0 || output[|output|-1] <= b[j])
    decreases |a| - i + |b| - j
  {
    if i >= |a| {
      output := output + [b[j]];
      j := j + 1;
    } else if j >= |b| {
      output := output + [a[i]];
      i := i + 1;
    } else if a[i] <= b[j] {
      output := output + [a[i]];
      i := i + 1;
    } else {
      output := output + [b[j]];
      j := j + 1;
    }
  }
  /* code modified by LLM (iteration 4): added final assertions to verify postcondition */
  assert multiset(output) == multiset(a[..i]) + multiset(b[..j]);
  assert i == |a| && j == |b|;
  assert multiset(a[..i]) + multiset(b[..j]) == multiset(a) + multiset(b);
  assert multiset(a) + multiset(b) == multiset(a + b);
}

//IMPL fast_sort
method fast_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
{
  output := input;
  if |output| <= 1 {
    return;
  }
  
  var n := |output|;
  while n > 1
    invariant 1 <= n <= |output|
    invariant multiset(output) == multiset(input)
    /* code modified by LLM (iteration 4): corrected bubble sort invariants */
    invariant IsSorted(output[n..])
    invariant forall i :: 0 <= i < n ==> forall j :: n <= j < |output| ==> output[i] <= output[j]
    decreases n
  {
    var newN := 0;
    var i := 1;
    while i < n
      invariant 1 <= i <= n
      invariant 0 <= newN <= i
      invariant multiset(output) == multiset(input)
      invariant IsSorted(output[n..])
      invariant forall k :: 0 <= k < n ==> forall j :: n <= j < |output| ==> output[k] <= output[j]
      /* code modified by LLM (iteration 4): strengthened inner loop invariants */
      invariant forall k :: 0 <= k < i-1 ==> output[k] <= output[i-1]
      invariant newN > 0 ==> (newN < i && output[newN-1] > output[newN])
      invariant newN == 0 ==> forall k :: 0 <= k < i-1 ==> output[k] <= output[k+1]
    {
      if output[i-1] > output[i] {
        /* code modified by LLM (iteration 4): proper swap maintaining all invariants */
        output := output[i-1 := output[i]][i := output[i-1]];
        newN := i;
      }
      i := i + 1;
    }
    /* code modified by LLM (iteration 4): added assertion to help prove termination */
    if newN == 0 {
      assert forall k :: 0 <= k < n-1 ==> output[k] <= output[k+1];
      assert IsSorted(output[..n]);
      assert n == |output|;
      assert IsSorted(output);
      return;
    }
    n := newN;
  }
  /* code modified by LLM (iteration 4): final assertion for postcondition */
  assert IsSorted(output);
  assert multiset(output) == multiset(input);
}