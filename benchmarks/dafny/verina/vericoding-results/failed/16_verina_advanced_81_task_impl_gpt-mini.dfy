// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define Sorted */
predicate Sorted(s: seq<int>)
{
  forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

/* helper modified by LLM (iteration 5): sequence to set conversion */
function SeqToSet(s: seq<int>): set<int>
{
  set x | x in s
}

/* helper modified by LLM (iteration 5): removing element from sequence corresponds to set difference, requires uniqueness */
lemma SeqRemoveElementSet(rem: seq<int>, idx: int)
  requires 0 <= idx < |rem|
  requires forall i,j :: 0 <= i < j < |rem| ==> rem[i] != rem[j]
  ensures SeqToSet(rem[..idx] + rem[idx+1..]) == SeqToSet(rem) - { rem[idx] }
{
  // Prove pointwise membership equivalence; unfolding definitions of SeqToSet and concatenation
  assert forall v :: (v in SeqToSet(rem[..idx] + rem[idx+1..])) <==> (v in SeqToSet(rem) && v != rem[idx]);
  assert SeqToSet(rem[..idx] + rem[idx+1..]) == SeqToSet(rem) - { rem[idx] };
}

/* helper modified by LLM (iteration 5): appending singleton to sequence corresponds to adding element to set */
lemma SeqAppendSingletonSet(s: seq<int>, x: int)
  ensures SeqToSet(s + [x]) == SeqToSet(s) + { x }
{
  assert forall v :: v in SeqToSet(s + [x]) <==> (v in SeqToSet(s) || v == x);
}

/* helper modified by LLM (iteration 5): appending element preserves sortedness when element >= all in seq */
lemma AppendPreservesSorted(s: seq<int>, b: int)
  requires Sorted(s)
  requires forall a :: a in s ==> a <= b
  ensures Sorted(s + [b])
{
  assert forall i :: 0 <= i < |s + [b]| - 1 ==> (s + [b])[i] <= (s + [b])[i + 1];
}

// </vc-helpers>

// <vc-spec>
method UniqueSorted(arr: array<int>) returns (result: array<int>)
    ensures result.Length <= arr.Length
    ensures forall i :: 0 <= i < result.Length - 1 ==> result[i] <= result[i + 1]
    ensures forall x :: x in arr[..] <==> x in result[..]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): collect unique elements and produce a sorted array of uniques */
{
  var n := arr.Length;
  var seen: set<int> := {};
  var tmpSeq: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant seen == SeqToSet(tmpSeq)
    invariant forall p, q :: 0 <= p < q < |tmpSeq| ==> tmpSeq[p] != tmpSeq[q]
  {
    var x := arr[i];
    if x !in seen {
      tmpSeq := tmpSeq + [x];
      seen := seen + {x};
    }
    i := i + 1;
  }

  var rem := tmpSeq;
  var sortedSeq: seq<int> := [];
  while |rem| > 0
    invariant SeqToSet(sortedSeq) + SeqToSet(rem) == SeqToSet(tmpSeq)
    invariant Sorted(sortedSeq)
    invariant forall a, b :: a in sortedSeq && b in rem ==> a <= b
    invariant forall p, q :: 0 <= p < q < |rem| ==> rem[p] != rem[q]
  {
    var minIdx := 0;
    var j := 1;
    while j < |rem|
      invariant 1 <= j <= |rem|
      invariant 0 <= minIdx < |rem|
      invariant forall p :: 0 <= p < j ==> rem[minIdx] <= rem[p]
    {
      if rem[j] < rem[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    var picked := rem[minIdx];
    // update set and sequence invariants using lemmas
    SeqAppendSingletonSet(sortedSeq, picked);
    SeqRemoveElementSet(rem, minIdx);
    sortedSeq := sortedSeq + [picked];
    rem := rem[..minIdx] + rem[minIdx + 1..];
  }

  var k := |sortedSeq|;
  result := new int[k];
  var idx := 0;
  while idx < k
    invariant 0 <= idx <= k
    invariant forall p :: 0 <= p < idx ==> result[p] == sortedSeq[p]
  {
    result[idx] := sortedSeq[idx];
    idx := idx + 1;
  }
}

// </vc-code>
