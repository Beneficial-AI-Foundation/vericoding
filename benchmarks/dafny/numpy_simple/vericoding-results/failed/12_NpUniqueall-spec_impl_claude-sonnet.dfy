// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed helper functions and added stronger lemmas for verification */
function contains(arr: array<int>, val: int): bool
    reads arr
{
    exists i :: 0 <= i < arr.Length && arr[i] == val
}

predicate isUniqueUpTo(arr: array<int>, n: int)
    reads arr
    requires 0 <= n <= arr.Length
{
    forall i, j :: 0 <= i < n && 0 <= j < n && i != j ==> arr[i] != arr[j]
}

lemma uniqueExtension(unique: array<int>, count: int, newVal: int)
    requires 0 <= count < unique.Length
    requires isUniqueUpTo(unique, count)
    requires forall k :: 0 <= k < count ==> unique[k] != newVal
    ensures unique[count] := newVal; isUniqueUpTo(unique, count + 1)
{}

lemma coveragePreservation(arr: array<int>, unique: array<int>, i: int, count: int, found: bool)
    requires 0 <= i < arr.Length
    requires 0 <= count <= unique.Length
    requires forall k :: 0 <= k < i ==> exists l :: 0 <= l < count && unique[l] == arr[k]
    requires found ==> exists l :: 0 <= l < count && unique[l] == arr[i]
    requires !found ==> forall l :: 0 <= l < count ==> unique[l] != arr[i]
    ensures found ==> forall k :: 0 <= k <= i ==> exists l :: 0 <= l < count && unique[l] == arr[k]
    ensures !found ==> (forall k :: 0 <= k < i ==> exists l :: 0 <= l < count + 1 && (if l < count then unique[l] else arr[i]) == arr[k]) && (forall k :: 0 <= k <= i ==> exists l :: 0 <= l < count + 1 && (if l < count then unique[l] else arr[i]) == arr[k])
{}
// </vc-helpers>

// <vc-spec>
method UniqueAll(arr: array<int>) returns (ret: array<int>)
    ensures
        ret.Length <= arr.Length &&
        (forall i :: 0 <= i < arr.Length ==> exists j :: 0 <= j < ret.Length && ret[j] == arr[i]) &&
        (forall i, j :: 0 <= i < ret.Length && 0 <= j < i ==> ret[i] != ret[j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): strengthened invariants and added assertions for verification */
    var unique := new int[arr.Length];
    var count := 0;
    
    for i := 0 to arr.Length
        invariant 0 <= count <= i <= arr.Length
        invariant isUniqueUpTo(unique, count)
        invariant forall k :: 0 <= k < i ==> exists l :: 0 <= l < count && unique[l] == arr[k]
        invariant forall k :: 0 <= k < count ==> exists l :: 0 <= l < arr.Length && unique[k] == arr[l]
    {
        var found := false;
        var j := 0;
        while j < count
            invariant 0 <= j <= count
            invariant found ==> exists k :: 0 <= k < j && unique[k] == arr[i]
            invariant !found ==> forall k :: 0 <= k < j ==> unique[k] != arr[i]
        {
            if unique[j] == arr[i] {
                found := true;
                break;
            }
            j := j + 1;
        }
        
        if !found {
            assert forall k :: 0 <= k < count ==> unique[k] != arr[i];
            unique[count] := arr[i];
            assert forall k :: 0 <= k <= i ==> exists l :: 0 <= l < count + 1 && unique[l] == arr[k];
            count := count + 1;
        }
    }
    
    ret := new int[count];
    for i := 0 to count
        invariant 0 <= i <= count
        invariant forall k :: 0 <= k < i ==> ret[k] == unique[k]
    {
        ret[i] := unique[i];
    }
    
    assert forall i :: 0 <= i < arr.Length ==> exists j :: 0 <= j < count && unique[j] == arr[i];
    assert forall i :: 0 <= i < ret.Length ==> ret[i] == unique[i];
}
// </vc-code>
