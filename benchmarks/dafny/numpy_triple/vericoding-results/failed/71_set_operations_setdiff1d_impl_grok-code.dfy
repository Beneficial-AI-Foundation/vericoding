// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix invariants in sort method to prove ensures clauses */
method sort(vals: seq<int>) returns (sortedVals: seq<int>)
  ensures forall i,j :: 0 <= i < j < |sortedVals| ==> sortedVals[i] <= sortedVals[j]
  ensures multiset(vals) == multiset(sortedVals)
  ensures forall x :: x in vals <==> x in sortedVals
  ensures forall i,j :: 0 <= i < j < |sortedVals| ==> sortedVals[i] != sortedVals[j]
{
  if |vals| == 0 {
    sortedVals := [];
  } else {
    sortedVals := [vals[0]];
    var i := 1;
    while i < |vals|
      invariant 1 <= i <= |vals|
      invariant forall j,k :: 0 <= j < k < |sortedVals| ==> sortedVals[j] <= sortedVals[k]
      invariant multiset(sortedVals) == multiset(vals[..i])
      invariant forall x :: x in sortedVals <==> x in vals[..i]
      invariant forall p,q :: 0 <= p < q < |sortedVals| ==> sortedVals[p] != sortedVals[q]
    {
      var key := vals[i];
      var j := |sortedVals| - 1;
      while j >= 0 && sortedVals[j] > key
        invariant -1 <= j <= |sortedVals| - 1
        invariant forall p,q :: 0 <= p < q < |sortedVals| ==> sortedVals[p] <= sortedVals[q]
        invariant multiset(sortedVals) == multiset(vals[..i])
        invariant forall p,q :: 0 <= p < q < |sortedVals| ==> sortedVals[p] != sortedVals[q]
      {
        j := j - 1;
      }
      sortedVals := sortedVals[..j+1] + [key] + sortedVals[j+1..];
      i := i + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method setdiff1d(ar1: seq<int>, ar2: seq<int>) returns (result: seq<int>)
    // Each element in result is from ar1 and not in ar2
    ensures forall i :: 0 <= i < |result| ==> 
        (exists j :: 0 <= j < |ar1| && result[i] == ar1[j]) &&
        (forall k :: 0 <= k < |ar2| ==> result[i] != ar2[k])
    
    // No duplicates in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    
    // Result is sorted in ascending order
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    
    // All unique values from ar1 not in ar2 are included in result
    ensures forall val {:trigger val in ar1} :: 
        ((exists i :: 0 <= i < |ar1| && ar1[i] == val) && 
         (forall j :: 0 <= j < |ar2| ==> ar2[j] != val)) ==>
        (exists k :: 0 <= k < |result| && result[k] == val)
    
    // Completeness: result contains exactly the values that should be there
    ensures forall val :: 
        (val in result) <==> 
        (val in ar1 && val !in ar2)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed set comprehension syntax to use Dafny new style */
{
  var ar2Set : set<int> := (set val | val in ar2);
  var uniqueSeq : seq<int> := [];
  var added : set<int> := {};
  var i : int := 0;
  while i < |ar1|
    invariant 0 <= i <= |ar1|
    invariant forall j :: 0 <= j < |uniqueSeq| ==> uniqueSeq[j] in ar1
    invariant forall j :: 0 <= j < |uniqueSeq| ==> uniqueSeq[j] !in ar2Set
    invariant forall j,k :: 0 <= j < k < |uniqueSeq| ==> uniqueSeq[j] != uniqueSeq[k]
    invariant forall val :: val in uniqueSeq <==> val in added
    invariant added subseteq (set val | val in ar1)
    invariant forall j :: 0 <= j < i ==> (ar1[j] !in ar2Set && ar1[j] !in added) ==> ar1[j] in uniqueSeq
  {
    if ar1[i] !in ar2Set && ar1[i] !in added {
      uniqueSeq := uniqueSeq + [ar1[i]];
      added := added + {ar1[i]};
    }
    i := i + 1;
  }
  result := sort(uniqueSeq);
}
// </vc-code>
