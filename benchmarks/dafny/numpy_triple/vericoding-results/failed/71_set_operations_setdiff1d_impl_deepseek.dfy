// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax errors in quicksort and filterOutValues functions */
predicate isSorted(s: seq<int>)
  ensures isSorted(s) <==> (forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j])
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function containsAllUniqueValues(s: seq<int>): bool
  ensures containsAllUniqueValues(s) <==> (forall i,j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function quicksort(s: seq<int>): seq<int>
  ensures |result| == |s|
  ensures isSorted(result)
  ensures multiset(s) == multiset(result)
{
  if |s| <= 1 then s
  else
    var pivot := s[|s|/2];
    var left : seq<int> := [x | x in s[0..|s|/2] where x <= pivot] + [x | x in s[|s|/2+1..|s|] where x <= pivot];
    var right : seq<int> := [x | x in s[0..|s|/2] where x > pivot] + [x | x in s[|s|/2+1..|s|] where x > pivot];
    quicksort(left) + [pivot] + quicksort(right)
}

function filterOutValues(ar1: seq<int>, ar2: seq<int>): seq<int>
  ensures forall i :: 0 <= i < |result| ==> 
      (exists j :: 0 <= j < |ar1| && result[i] == ar1[j]) &&
      (forall k :: 0 <= k < |ar2| ==> result[i] != ar2[k])
  ensures forall i,j :: 0 <= i < j < |result| ==> result[i] != result[j]
  ensures forall val :: val in result ==> (val in ar1 && val !in ar2)
{
  if |ar1| == 0 then []
  else if ar1[0] in ar2 then filterOutValues(ar1[1..], ar2)
  else if ar1[0] in filterOutValues(ar1[1..], ar2) then filterOutValues(ar1[1..], ar2)
  else [ar1[0]] + filterOutValues(ar1[1..], ar2)
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
/* code modified by LLM (iteration 5): Using corrected helper functions */
{
  var filtered := filterOutValues(ar1, ar2);
  result := quicksort(filtered);
}
// </vc-code>
