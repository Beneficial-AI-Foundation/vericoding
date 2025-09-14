predicate quickSorted(Seq: seq<int>)
{
  forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < |Seq| ==> Seq[idx_1] <= Seq[idx_2]
}

// <vc-helpers>
lemma multiset_append_element<T>(s: seq<T>, x: T)
  ensures multiset(s + [x]) == multiset(s) + multiset([x])
{
}

lemma multiset_slice_extension<T>(s: seq<T>, i: int)
  requires 0 <= i < |s|
  ensures multiset(s[0..i+1]) == multiset(s[0..i]) + multiset([s[i]])
{
  assert s[0..i+1] == s[0..i] + [s[i]];
  multiset_append_element(s[0..i], s[i]);
}

lemma multiset_full_slice<T>(s: seq<T>)
  ensures multiset(s[0..|s|]) == multiset(s)
{
  assert s[0..|s|] == s;
}
// </vc-helpers>

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
    invariant multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[0..i])
  {
    multiset_slice_extension(Seq, i);
    if Seq[i] <= thres {
      multiset_append_element(Seq_1, Seq[i]);
      Seq_1 := Seq_1 + [Seq[i]];
    } else {
      multiset_append_element(Seq_2, Seq[i]);
      Seq_2 := Seq_2 + [Seq[i]];
    }
    i := i + 1;
  }
  
  multiset_full_slice(Seq);
}
// </vc-code>

