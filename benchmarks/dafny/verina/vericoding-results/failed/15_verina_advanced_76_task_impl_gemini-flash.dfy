// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* DYNAMIC_PARAM_FIX removed by LLM (iteration 5): The DYNAMIC_PARAM_FIX was a placeholder and removed. */
function count(a: array<int>, x: int, start: int, end: int): nat
    requires 0 <= start <= end <= a.Length
{
    if start == end then 0
    else (if a[start] == x then 1 else 0) + count(a, x, start + 1, end)
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
/* code modified by LLM (iteration 5): Removed the `FIX_PARAM_TYPE` placeholder that was causing a compilation error. */
{
    // Step 1: Count frequencies of each number.
    // We'll use a map to store frequencies: Map<int, int>
    var frequencies := map[];
    for i := 0 to nums.Length-1
        invariant 0 <= i <= nums.Length
        invariant forall x | x in frequencies.Keys :: 1 <= frequencies[x]
        invariant forall x | x in frequencies.Keys :: x in nums[..i]
        invariant forall x | x in frequencies.Keys :: frequencies[x] == count(nums, x, 0, i)
    {
        var num := nums[i];
        if num in frequencies {
            frequencies := frequencies[num := frequencies[num] + 1];
        } else {
            frequencies := frequencies[num := 1];
        }
    }

    // Step 2: Create an array of (value, frequency) tuples.
    var items: array<(int, int)>;
    if |frequencies| > 0 {
        items := new array<(int, int)>(|frequencies|);
    } else {
        items := new array<(int, int)>(0);
    }
    
    var idx := 0;
    var keys_seq := frequencies.Keys.AsSeq(); // Convert set to sequence for indexing

    for i := 0 to |keys_seq|-1
        invariant 0 <= idx <= items.Length
        invariant idx == i
        invariant forall l, m :: 0 <= l < m < idx ==> items[l].0 != items[m].0
        invariant forall l :: 0 <= l < idx ==> items[l].0 in frequencies.Keys && items[l].1 == frequencies[items[l].0]
    {
        var key := keys_seq[i];
        items[idx] := (key, frequencies[key]);
        idx := idx + 1;
    }

    // Step 3: Sort the items by frequency in descending order.
    // This is a bubble sort, simple enough for Dafny, but inefficient.
    // A real implementation would use a better sort or a min-heap.
    for i := 0 to items.Length-2
        invariant 0 <= i < items.Length
        invariant (forall u, v :: items.Length - i - 1 <= u < v < items.Length ==> items[u].1 >= items[v].1)
        invariant forall x :: (0 <= x < items.Length) ==> items[x].0 in frequencies.Keys && items[x].1 == frequencies[items[x].0]
        invariant forall x, y :: (0 <= x < items.Length && 0 <= y < items.Length && x != y) ==> items[x].0 != items[y].0
    {
        for j := 0 to items.Length-2-i
            invariant 0 <= j <= items.Length-1-i
            invariant (forall u, v :: items.Length - i - 1 <= u < v < items.Length ==> items[u].1 >= items[v].1)
            invariant forall x :: (0 <= x < items.Length) ==> items[x].0 in frequencies.Keys && items[x].1 == frequencies[items[x].0]
            invariant forall x, y :: (0 <= x < items.Length && 0 <= y < items.Length && x != y) ==> items[x].0 != items[y].0
        {
            if items[j].1 < items[j+1].1 {
                var temp := items[j];
                items[j] := items[j+1];
                items[j+1] := temp;
            }
        }
    }
    
    // Step 4: Extract the k most frequent elements.
    result := new int[k];
    for i := 0 to k-1
        invariant 0 <= i <= k
        invariant forall x :: 0 <= x < i ==> result[x] in nums[..]
        invariant forall x, y :: 0 <= x < y < i ==> result[x] != result[y]
    {
        result[i] := items[i].0;
    }

    // The requires k <= |set i | 0 <= i < nums.Length :: nums[i]| ensures that there are at least k unique elements.
    // The sorting ensures that the k selected elements correspond to the highest frequencies.
    // The construction for result ensures it has length k and its elements come from nums.
    // The final loop invariant for result ensures that result[..i] contains unique elements.
    // And because we pick from unique keys of the map, and k <= number of unique keys, we satisfy the unique requirement.
}
// </vc-code>
