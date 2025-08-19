predicate IsSorted( s: seq<int> )
{
  forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

//IMPL SPEC
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
  ensures multiset(r) == multiset(s)
  ensures IsSorted(r)
{
  r := [];
  
  for i := 0 to |s|
    invariant multiset(r) == multiset(s[..i])
    invariant IsSorted(r)
  {
    var x := s[i];
    var j := 0;
    
    while j < |r| && r[j] <= x
      invariant 0 <= j <= |r|
      invariant forall k | 0 <= k < j :: r[k] <= x
      invariant multiset(r) == multiset(s[..i])
    {
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 4): added lemma calls and proper multiset reasoning */
    MultisetConcatenationLemma(r[..j], [x], r[j..]);
    assert r == r[..j] + r[j..];
    assert multiset(r) == multiset(r[..j] + r[j..]);
    assert multiset(r[..j] + [x] + r[j..]) == multiset(r[..j]) + multiset([x]) + multiset(r[j..]);
    assert multiset(r[..j]) + multiset(r[j..]) == multiset(r);
    assert multiset(r[..j] + [x] + r[j..]) == multiset(r) + multiset([x]);
    
    assert x == s[i];
    assert multiset([x]) == multiset([s[i]]);
    SequenceSliceLemma(s, i);
    assert multiset(s[..i+1]) == multiset(s[..i]) + multiset([s[i]]);
    
    r := r[..j] + [x] + r[j..];
  }
  
  /* code modified by LLM (iteration 4): added assertion to help prove postcondition */
  assert multiset(r) == multiset(s[..|s|]);
  SequenceFullSliceLemma(s);
  assert s[..|s|] == s;
  assert multiset(s[..|s|]) == multiset(s);
}

/* code modified by LLM (iteration 4): added helper lemma for multiset concatenation */
lemma MultisetConcatenationLemma<T>(a: seq<T>, b: seq<T>, c: seq<T>)
  ensures multiset(a + b + c) == multiset(a) + multiset(b) + multiset(c)
{
  // Dafny can prove this automatically
}

/* code modified by LLM (iteration 4): added helper lemma for sequence slice multiset property */
lemma SequenceSliceLemma<T>(s: seq<T>, i: int)
  requires 0 <= i < |s|
  ensures multiset(s[..i+1]) == multiset(s[..i]) + multiset([s[i]])
{
  assert s[..i+1] == s[..i] + [s[i]];
}

/* code modified by LLM (iteration 4): added helper lemma for full sequence slice */
lemma SequenceFullSliceLemma<T>(s: seq<T>)
  ensures s[..|s|] == s
{
  // Dafny can prove this automatically
}