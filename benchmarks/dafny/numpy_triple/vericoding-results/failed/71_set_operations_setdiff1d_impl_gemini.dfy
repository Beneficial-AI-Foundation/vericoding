// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implementing with an iterative loop to be more robust for verification */
method InsertSorted(s: seq<int>, val: int) returns (res: seq<int>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
    requires val !in s
    ensures |res| == |s| + 1
    ensures forall i, j :: 0 <= i < j < |res| ==> res[i] < res[j]
    ensures forall x :: x in res <==> x in s || x == val
{
    var i := 0;
    while i < |s| && s[i] < val
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> s[j] < val
    {
        i := i + 1;
    }
    res := s[..i] + [val] + s[i..];
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
{
  /* code modified by LLM (iteration 5): split loop invariant into two implications */
  result := [];
  var i := 0;
  while i < |ar1|
    invariant 0 <= i <= |ar1|
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
    invariant forall x :: x in result ==> (x in ar1[..i] && x !in ar2)
    invariant forall x :: (x in ar1[..i] && x !in ar2) ==> x in result
  {
    var val := ar1[i];
    if val !in ar2 && val !in result {
      result := InsertSorted(result, val);
    }
    i := i + 1;
  }
}
// </vc-code>
