// ATOM 
predicate IsSorted(s:seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}


// ATOM 

predicate SortSpec(input:seq<int>, output:seq<int>)
{
  && IsSorted(output)
  && multiset(output) == multiset(input)
}


//lemma SequenceConcat(s:seq<int>, pivot:int)
//  requires 0<=pivot<|s|
//  ensures s[..pivot] + s[pivot..] == s
//{
//}

//ATOM_PLACEHOLDER_merge_sort

//ATOM_PLACEHOLDER_merge

// IMPL 

method fast_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
{
  if |input| <= 1 {
    output := input;
  } else {
    var sorted := input;
    var n := |sorted|;
    var i := 0;
    
    while i < n - 1
      invariant 0 <= i <= n - 1
      invariant |sorted| == n == |input|
      invariant multiset(sorted) == multiset(input)
      invariant forall k :: 0 <= k < i ==> sorted[k] <= sorted[k + 1]
      invariant forall k1, k2 :: 0 <= k1 < i && i <= k2 < n ==> sorted[k1] <= sorted[k2]
    {
      var minIdx := i;
      var j := i + 1;
      
      while j < n
        invariant i <= minIdx < n
        invariant i + 1 <= j <= n
        invariant |sorted| == n
        invariant multiset(sorted) == multiset(input)
        invariant forall k :: i <= k < j ==> sorted[minIdx] <= sorted[k]
      {
        if sorted[j] < sorted[minIdx] {
          minIdx := j;
        }
        j := j + 1;
      }
      
      if minIdx != i {
        var temp := sorted[i];
        sorted := sorted[i := sorted[minIdx]][minIdx := temp];
      }
      
      i := i + 1;
    }
    
    output := sorted;
  }
}