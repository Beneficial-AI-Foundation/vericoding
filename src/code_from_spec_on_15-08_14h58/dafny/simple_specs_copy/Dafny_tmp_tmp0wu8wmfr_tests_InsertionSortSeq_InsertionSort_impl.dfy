//ATOM
// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is

predicate IsSorted( s: seq<int> )
{
  forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

//IMPL 
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
  ensures multiset(r) == multiset(s)
  ensures IsSorted(r)
{
  r := [];
  for i := 0 to |s|
    invariant multiset(r) == multiset(s[..i])
    invariant IsSorted(r)
  {
    r := Insert(r, s[i]);
    /* code modified by LLM (iteration 1): Added assertion to help prove multiset property is maintained */
    assert s[..i+1] == s[..i] + [s[i]];
    assert multiset(s[..i+1]) == multiset(s[..i]) + multiset([s[i]]);
  }
  /* code modified by LLM (iteration 2): Added assertion to prove that s[..|s|] == s */
  assert s[..|s|] == s;
}

method Insert(sorted: seq<int>, x: int) returns (result: seq<int>)
  requires IsSorted(sorted)
  ensures multiset(result) == multiset(sorted) + multiset([x])
  ensures IsSorted(result)
{
  var i := 0;
  while i < |sorted| && sorted[i] < x
    invariant 0 <= i <= |sorted|
    invariant forall k | 0 <= k < i :: sorted[k] < x
  {
    i := i + 1;
  }
  result := sorted[..i] + [x] + sorted[i..];
  /* code modified by LLM (iteration 1): Added assertions to help prove multiset postcondition */
  assert sorted == sorted[..i] + sorted[i..];
  assert multiset(sorted) == multiset(sorted[..i]) + multiset(sorted[i..]);
  assert multiset(result) == multiset(sorted[..i]) + multiset([x]) + multiset(sorted[i..]);
  assert multiset(result) == multiset(sorted) + multiset([x]);
}