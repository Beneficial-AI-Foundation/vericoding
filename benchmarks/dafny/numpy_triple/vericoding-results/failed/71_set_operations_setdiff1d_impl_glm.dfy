// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Contains(s: seq<int>, x: int): bool {
  x in s
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
  /* code modified by LLM (iteration 5): Fixed parse error by removing 'then' keyword in if condition */
  result := [];
  for i := 0 to |ar1|
    invariant |result| <= i
    invariant forall k :: 0 <= k < |result| ==> 
      (exists j :: 0 <= j < i && ar1[j] == result[k]) && 
      (forall l :: 0 <= l < |ar2| ==> result[k] != ar2[l])
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] <= result[l]
    invariant forall val :: 
      ((exists j :: 0 <= j < i && ar1[j] == val) && 
       (forall j :: 0 <= j < |ar2| ==> ar2[j] != val)) ==>
      (exists j :: 0 <= j < |result| && result[j] == val)
  {
    var val := ar1[i];
    if !Contains(ar2, val) && !Contains(result, val) {
      var j := 0;
      while j < |result| && result[j] < val
        invariant 0 <= j <= |result|
        invariant forall k :: 0 <= k < j ==> result[k] < val
      {
        j := j + 1;
      }
      result := result[0..j] + [val] + result[j..];
    }
  }
}
// </vc-code>
