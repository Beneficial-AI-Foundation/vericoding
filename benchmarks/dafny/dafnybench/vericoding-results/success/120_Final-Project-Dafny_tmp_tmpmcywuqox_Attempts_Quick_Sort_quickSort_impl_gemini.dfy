// <vc-preamble>
predicate quickSorted(Seq: seq<int>)
{
  forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < |Seq| ==> Seq[idx_1] <= Seq[idx_2]
}

method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added simple proof body */
lemma MultisetHeadAndTail(s: seq<int>)
  requires |s| >= 1
  ensures multiset(s) == multiset([s[0]]) + multiset(s[1..])
{
  assert s == [s[0]] + s[1..];
}
// </vc-helpers>

// <vc-spec>
method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq) == multiset(Seq')
  decreases |Seq|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): logic is sound with fixed helper */
  if |Seq| <= 1 {
    Seq' := Seq;
  } else {
    var pivot := Seq[0];
    var rest := Seq[1..];
    
    MultisetHeadAndTail(Seq); // Establishes multiset(Seq) == multiset([pivot]) + multiset(rest)

    var lesser, greater := threshold(pivot, rest);
    // Inferred: multiset(rest) == multiset(lesser) + multiset(greater)

    var sorted_lesser := quickSort(lesser);
    // Inferred: multiset(sorted_lesser) == multiset(lesser)

    var sorted_greater := quickSort(greater);
    // Inferred: multiset(sorted_greater) == multiset(greater)

    Seq' := sorted_lesser + [pivot] + sorted_greater;
    // multiset(Seq') == multiset(sorted_lesser) + multiset([pivot]) + multiset(sorted_greater)
    //               == multiset(lesser) + multiset([pivot]) + multiset(greater)
    //               == multiset([pivot]) + multiset(rest)
    //               == multiset(Seq)
  }
}
// </vc-code>
