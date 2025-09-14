// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fix IsSorted to work with sequences */
function Contains(arr: array<int>, x: int): bool reads arr
{
    exists i :: 0 <= i < arr.Length && arr[i] == x
}

predicate IsSorted(arr: seq<int>)
{
    forall i :: 0 <= i < |arr| - 1 ==> arr[i] <= arr[i + 1]
}
// </vc-helpers>

// <vc-spec>
method UniqueSorted(arr: array<int>) returns (result: array<int>)
    ensures result.Length <= arr.Length
    ensures forall i :: 0 <= i < result.Length - 1 ==> result[i] <= result[i + 1]
    ensures forall x :: x in arr[..] <==> x in result[..]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fix sequence access in loop invariant */
{
    // Handle empty array case
    if arr.Length == 0 {
        result := new int[0];
        return;
    }
    
    // Count unique elements
    var count := 0;
    for i := 0 to arr.Length
        invariant 0 <= count <= i
    {
        var unique := true;
        for j := 0 to i
            invariant unique == (forall k :: 0 <= k < j ==> i != k && arr[i] != arr[k])
        {
            if i != j && arr[i] == arr[j]
            {
                unique := false;
            }
        }
        if unique
        {
            count := count + 1;
        }
    }
    
    // Create and fill the result array
    result := new int[count];
    var idx := 0;
    for i := 0 to arr.Length
        invariant 0 <= idx <= count
        invariant idx == count ==> i == arr.Length
    {
        var unique := true;
        for j := 0 to i
            invariant unique == (forall k :: 0 <= k < j ==> i != k && arr[i] != arr[k])
        {
            if i != j && arr[i] == arr[j]
            {
                unique := false;
            }
        }
        if unique
        {
            result[idx] := arr[i];
            idx := idx + 1;
        }
    }
    
    // Sort the result array using selection sort
    for i := 0 to result.Length - 1
        invariant IsSorted(result[0..i])
        invariant forall x :: x in result[0..i] ==> x in arr[..]
    {
        var minIndex := i;
        for j := i + 1 to result.Length - 1
            invariant i <= minIndex < result.Length
            invariant forall k :: i <= k < j ==> result[minIndex] <= result[k]
        {
            if result[j] < result[minIndex]
            {
                minIndex := j;
            }
        }
        if minIndex != i
        {
            var temp := result[i];
            result[i] := result[minIndex];
            result[minIndex] := temp;
        }
    }
}
// </vc-code>
