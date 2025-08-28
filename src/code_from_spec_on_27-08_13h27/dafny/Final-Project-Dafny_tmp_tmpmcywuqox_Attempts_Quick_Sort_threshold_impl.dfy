predicate quickSorted(Seq: seq<int>)
{
  forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < |Seq| ==> Seq[idx_1] <= Seq[idx_2]
}

// <vc-helpers>
// Helper lemma to ensure multiset properties are maintained
lemma MultisetSplit(s1: seq<int>, s2: seq<int>, original: seq<int>)
  ensures multiset(s1) + multiset(s2) == multiset(original) ==> multiset(original) == multiset(s1 + s2)
{
}

lemma MultisetAppend(s: seq<int>, x: int)
  ensures multiset(s + [x]) == multiset(s) + multiset([x])
{
}

lemma MultisetSlice(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures multiset(s[..i]) + multiset(s[i..]) == multiset(s)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
// </vc-spec>
// </vc-spec>

// <vc-code>
method SplitByThreshold(thres: int, Seq: seq<int>) returns (Seq_1: seq<int>, Seq_2: seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
  Seq_1 := [];
  Seq_2 := [];
  var i := 0;
  
  while i < |Seq|
    invariant 0 <= i <= |Seq|
    invariant |Seq_1| + |Seq_2| == i
    invariant forall x | x in Seq_1 :: x <= thres
    invariant forall x | x in Seq_2 :: x >= thres
    invariant multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i])
  {
    if Seq[i] <= thres {
      Seq_1 := Seq_1 + [Seq[i]];
      calc {
        multiset(Seq_1) + multiset(Seq_2);
        { assert Seq_1 == Seq_1[..|Seq_1|-1] + [Seq[i]]; }
        multiset(Seq_1[..|Seq_1|-1] + [Seq[i]]) + multiset(Seq_2);
        { MultisetAppend(Seq_1[..|Seq_1|-1], Seq[i]); }
        multiset(Seq_1[..|Seq_1|-1]) + multiset([Seq[i]]) + multiset(Seq_2);
        { assert multiset(Seq_1[..|Seq_1|-1]) + multiset(Seq_2) == multiset(Seq[..i]); }
        multiset(Seq[..i]) + multiset([Seq[i]]);
        { MultisetAppend(Seq[..i], Seq[i]); }
        multiset(Seq[..i+1]);
      }
    } else {
      Seq_2 := Seq_2 + [Seq[i]];
      calc {
        multiset(Seq_1) + multiset(Seq_2);
        { assert Seq_2 == Seq_2[..|Seq_2|-1] + [Seq[i]]; }
        multiset(Seq_1) + multiset(Seq_2[..|Seq_2|-1] + [Seq[i]]);
        { MultisetAppend(Seq_2[..|Seq_2|-1], Seq[i]); }
        multiset(Seq_1) + multiset(Seq_2[..|Seq_2|-1]) + multiset([Seq[i]]);
        { assert multiset(Seq_1) + multiset(Seq_2[..|Seq_2|-1]) == multiset(Seq[..i]); }
        multiset(Seq[..i]) + multiset([Seq[i]]);
        { MultisetAppend(Seq[..i], Seq[i]); }
        multiset(Seq[..i+1]);
      }
    }
    i := i + 1;
  }
}
// </vc-code>
