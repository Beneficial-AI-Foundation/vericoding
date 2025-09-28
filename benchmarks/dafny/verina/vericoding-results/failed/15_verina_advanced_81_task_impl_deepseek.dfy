// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed sorted function and removeDuplicatesSorted postconditions */
function sorted(a: seq<int>): bool {
  if |a| <= 1 then true
  else a[0] <= a[1] && sorted(a[1..])
}

predicate unique(a: seq<int>) {
  forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j]
}

function removeDuplicatesSorted(a: seq<int>): seq<int>
  requires sorted(a)
  ensures |removeDuplicatesSorted(a)| <= |a|
  ensures forall x :: x in a <==> x in removeDuplicatesSorted(a)
  ensures sorted(removeDuplicatesSorted(a))
  ensures forall i :: 0 <= i < |removeDuplicatesSorted(a)| - 1 ==> removeDuplicatesSorted(a)[i] < removeDuplicatesSorted(a)[i + 1]
{
  if |a| <= 1 then a
  else if a[0] == a[1] then removeDuplicatesSorted(a[1..])
  else [a[0]] + removeDuplicatesSorted(a[1..])
}

lemma BubbleSortMaintainsElements(arr: array<int>, sortedArr: array<int>)
  requires sortedArr.Length == arr.Length
  ensures forall x :: x in arr[..] <==> x in sortedArr[..]
{
}

lemma SortedSliceSorted(a: seq<int>, n: int)
  requires sorted(a) && 0 <= n <= |a|
  ensures sorted(a[n..])
{
}

lemma SortedHeadLeq(a: seq<int>)
  requires sorted(a) && |a| >= 2
  ensures a[0] <= a[1]
{
  if |a| >= 2 {
    assert sorted(a);
  }
}

lemma SortedTailSorted(a: seq<int>)
  requires sorted(a) && |a| >= 1
  ensures sorted(a[1..])
{
  if |a| >= 2 {
    assert sorted(a);
    assert a[0] <= a[1];
  }
}
// </vc-helpers>

// <vc-spec>
method UniqueSorted(arr: array<int>) returns (result: array<int>)
    ensures result.Length <= arr.Length
    ensures forall i :: 0 <= i < result.Length - 1 ==> result[i] <= result[i + 1]
    ensures forall x :: x in arr[..] <==> x in result[..]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): improved bubble sort with proper sorting invariant and sorted proof */
{
  var sortedArr := new int[arr.Length];
  var seqSortedArr: seq<int>;
  
  if arr.Length > 0 {
    for i := 0 to arr.Length - 1
        invariant sortedArr.Length == arr.Length
        invariant forall j :: 0 <= j < i ==> sortedArr[j] == arr[j]
    {
        sortedArr[i] := arr[i];
    }
    
    seqSortedArr := sortedArr[..];
    
    // Bubble sort with proper sorting verification
    for i := 0 to sortedArr.Length - 1
        invariant sortedArr.Length == arr.Length
        invariant sorted(sortedArr[..])
    {
        var swapped := false;
        for j := 0 to sortedArr.Length - 2 - i
            invariant sorted(sortedArr[..j + 1])
            invariant forall k, l :: 0 <= k <= j < l < sortedArr.Length ==> sortedArr[k] <= sortedArr[l]
        {
            if sortedArr[j] > sortedArr[j + 1] {
                var temp := sortedArr[j];
                sortedArr[j] := sortedArr[j + 1];
                sortedArr[j + 1] := temp;
                swapped := true;
            }
        }
        if !swapped {
            break;
        }
    }
    seqSortedArr := sortedArr[..];
  } else {
    seqSortedArr := [];
  }
  
  // Prove the sequence is sorted before calling removeDuplicatesSorted
  assert sorted(seqSortedArr);
  var uniqueSeq := removeDuplicatesSorted(seqSortedArr);
  result := new int[|uniqueSeq|];
  if |uniqueSeq| > 0 {
    for i := 0 to |uniqueSeq| - 1
        invariant result.Length == |uniqueSeq|
        invariant forall j :: 0 <= j < i ==> result[j] == uniqueSeq[j]
    {
        result[i] := uniqueSeq[i];
    }
  }
}
// </vc-code>
