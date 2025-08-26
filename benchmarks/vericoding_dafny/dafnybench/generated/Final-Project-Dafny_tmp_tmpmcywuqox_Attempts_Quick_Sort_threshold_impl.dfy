lemma MultisetSliceEquality(s: seq<int>)
  ensures multiset(s[..|s|]) == multiset(s)
{
  assert s[..|s|] == s;
}

lemma MultisetAppendLemma(s1: seq<int>, elem: int)
  ensures multiset(s1 + [elem]) == multiset(s1) + multiset([elem])
{
}

lemma SliceExtensionLemma(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures s[..i+1] == s[..i] + [s[i]]
  ensures multiset(s[..i+1]) == multiset(s[..i]) + multiset([s[i]])
{
  assert s[..i+1] == s[..i] + [s[i]];
  MultisetAppendLemma(s[..i], s[i]);
}
</vc-helpers>

// <vc-spec>
method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
// </vc-spec>
// <vc-code>
{
  Seq_1 := [];
  Seq_2 := [];
  
  var i := 0;
  while i < |Seq|
    invariant 0 <= i <= |Seq|
    invariant forall x | x in Seq_1 :: x <= thres
    invariant forall x | x in Seq_2 :: x >= thres
    invariant |Seq_1| + |Seq_2| == i
    invariant multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i])
  {
    // Establish the relationship for the next iteration
    SliceExtensionLemma(Seq, i);
    
    if Seq[i] <= thres {
      var old_Seq_1 := Seq_1;
      Seq_1 := Seq_1 + [Seq[i]];
      MultisetAppendLemma(old_Seq_1, Seq[i]);
      assert multiset(Seq_1) == multiset(old_Seq_1) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(old_Seq_1) + multiset(Seq_2) + multiset([Seq[i]]);
      assert multiset(old_Seq_1) + multiset(Seq_2) == multiset(Seq[..i]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i]) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i+1]);
    } else {
      var old_Seq_2 := Seq_2;
      Seq_2 := Seq_2 + [Seq[i]];
      MultisetAppendLemma(old_Seq_2, Seq[i]);
      assert multiset(Seq_2) == multiset(old_Seq_2) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq_1) + multiset(old_Seq_2) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(old_Seq_2) == multiset(Seq[..i]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i]) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i+1]);
    }
    i := i + 1;
  }
  
  // Help Dafny see that Seq[..i] == Seq when i == |Seq|
  MultisetSliceEquality(Seq);
  assert i == |Seq|;
  assert Seq[..i] == Seq;
}
// </vc-code>