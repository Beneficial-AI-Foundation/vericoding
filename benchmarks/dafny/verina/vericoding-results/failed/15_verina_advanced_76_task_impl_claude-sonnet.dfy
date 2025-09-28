// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added min function for compilation */
function min(a: int, b: int): int
{
    if a <= b then a else b
}

predicate ValidFrequencyCount(nums: array<int>, uniqueNums: array<int>, frequencies: array<int>, uniqueCount: int)
    reads nums, uniqueNums, frequencies
{
    0 <= uniqueCount <= nums.Length &&
    uniqueCount <= uniqueNums.Length &&
    uniqueCount <= frequencies.Length &&
    (forall i :: 0 <= i < uniqueCount ==> frequencies[i] > 0) &&
    (forall i, j :: 0 <= i < j < uniqueCount ==> uniqueNums[i] != uniqueNums[j]) &&
    (forall x :: x in nums[..] ==> exists i :: 0 <= i < uniqueCount && uniqueNums[i] == x)
}

predicate ValidSelection(nums: array<int>, result: array<int>, selected: int)
    reads nums, result
{
    0 <= selected <= result.Length &&
    (forall i :: 0 <= i < selected ==> result[i] in nums[..]) &&
    (forall i, j :: 0 <= i < j < selected ==> result[i] != result[j])
}

predicate IsUniqueInArray(arr: array<int>, val: int, upTo: int)
    reads arr
{
    forall i :: 0 <= i < upTo ==> arr[i] != val
}
// </vc-helpers>

// <vc-spec>
method TopKFrequent(nums: array<int>, k: nat) returns (result: array<int>)
    requires k <= |set i | 0 <= i < nums.Length :: nums[i]|
    ensures result.Length == k
    ensures forall x :: x in result[..] ==> x in nums[..]
    ensures forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed problematic invariant for simplicity */
    if k == 0 {
        result := new int[0];
        return;
    }
    
    var uniqueNums := new int[nums.Length];
    var frequencies := new int[nums.Length];
    var uniqueCount := 0;
    
    // Count frequencies
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= uniqueCount <= nums.Length
        invariant uniqueCount <= i
        invariant forall idx :: 0 <= idx < uniqueCount ==> frequencies[idx] >= 1
        invariant forall idx1, idx2 :: 0 <= idx1 < idx2 < uniqueCount ==> uniqueNums[idx1] != uniqueNums[idx2]
        invariant forall x :: x in nums[..i] ==> exists idx :: 0 <= idx < uniqueCount && uniqueNums[idx] == x
    {
        var found := false;
        var foundIndex := -1;
        var j := 0;
        while j < uniqueCount && !found
            invariant 0 <= j <= uniqueCount
            invariant found <==> foundIndex >= 0
            invariant found ==> 0 <= foundIndex < j && uniqueNums[foundIndex] == nums[i]
            invariant !found ==> forall k :: 0 <= k < j ==> uniqueNums[k] != nums[i]
        {
            if uniqueNums[j] == nums[i] {
                frequencies[j] := frequencies[j] + 1;
                found := true;
                foundIndex := j;
            }
            j := j + 1;
        }
        if !found {
            uniqueNums[uniqueCount] := nums[i];
            frequencies[uniqueCount] := 1;
            uniqueCount := uniqueCount + 1;
        }
        i := i + 1;
    }
    
    result := new int[k];
    
    // Simple selection of top k elements
    var selected := 0;
    var used := new bool[uniqueCount];
    
    while selected < k && selected < uniqueCount
        invariant 0 <= selected <= k
        invariant selected <= uniqueCount
        invariant forall idx :: 0 <= idx < selected ==> exists uidx :: 0 <= uidx < uniqueCount && uniqueNums[uidx] == result[idx]
        invariant forall idx1, idx2 :: 0 <= idx1 < idx2 < selected ==> result[idx1] != result[idx2]
        invariant forall idx :: 0 <= idx < selected ==> exists uidx :: 0 <= uidx < uniqueCount && uniqueNums[uidx] == result[idx] && used[uidx]
    {
        var maxFreq := -1;
        var maxIndex := -1;
        var idx := 0;
        while idx < uniqueCount
            invariant 0 <= idx <= uniqueCount
            invariant maxIndex == -1 || (0 <= maxIndex < uniqueCount && !used[maxIndex])
        {
            if !used[idx] && frequencies[idx] > maxFreq {
                maxFreq := frequencies[idx];
                maxIndex := idx;
            }
            idx := idx + 1;
        }
        
        if maxIndex >= 0 && maxIndex < uniqueCount {
            result[selected] := uniqueNums[maxIndex];
            used[maxIndex] := true;
            selected := selected + 1;
        } else {
            break;
        }
    }
    
    // Fill remaining slots by duplicating unique elements
    while selected < k
        invariant 0 <= selected <= k
        invariant uniqueCount > 0 ==> forall idx :: 0 <= idx < selected ==> exists uidx :: 0 <= uidx < uniqueCount && uniqueNums[uidx] == result[idx]
    {
        if uniqueCount > 0 {
            var cycleIndex := selected % uniqueCount;
            result[selected] := uniqueNums[cycleIndex];
        } else {
            result[selected] := 0;
        }
        selected := selected + 1;
    }
}
// </vc-code>
