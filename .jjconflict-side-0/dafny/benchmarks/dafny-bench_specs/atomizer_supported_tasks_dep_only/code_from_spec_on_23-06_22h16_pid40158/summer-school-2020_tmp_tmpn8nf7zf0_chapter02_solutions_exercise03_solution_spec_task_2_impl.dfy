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

// IMPL merge
method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures SortSpec(a+b, output)
{
  var i := 0;
  var j := 0;
  output := [];
  
  while i < |a| || j < |b|
    invariant 0 <= i <= |a|
    invariant 0 <= j <= |b|
    invariant IsSorted(output)
    invariant multiset(output) == multiset(a[..i]) + multiset(b[..j])
    /* code modified by LLM (iteration 4): corrected invariants for merge ordering */
    invariant i < |a| && |output| > 0 ==> output[|output|-1] <= a[i]
    invariant j < |b| && |output| > 0 ==> output[|output|-1] <= b[j]
  {
    if i >= |a| {
      /* code modified by LLM (iteration 4): simplified b-only case */
      output := output + [b[j]];
      j := j + 1;
    } else if j >= |b| {
      /* code modified by LLM (iteration 4): simplified a-only case */
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
  
  /* code modified by LLM (iteration 4): final assertions to establish postcondition */
  assert i == |a| && j == |b|;
  assert a[..i] == a && b[..j] == b;
  assert multiset(output) == multiset(a) + multiset(b);
  assert multiset(a + b) == multiset(a) + multiset(b);
}