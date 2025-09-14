method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
  assume{:axiom} false;
}

function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] == value then 1 else 0) + count(arr[1..], value)
}

// <vc-helpers>
predicate IsOrderPreserved<T(==)>(a: seq<T>, b: seq<T>, zero: T)
{
  (forall i, j :: 0 <= i < j < |a| && a[i] != zero && a[j] != zero ==>
    exists k, l :: 0 <= k < l < |b| && b[k] == a[i] && b[l] == a[j])
}
// </vc-helpers>

// <vc-spec>
method MoveZeroesToEnd(arr: array<int>)
    requires arr.Length >= 2
    modifies arr
    // Same size
    ensures arr.Length == old(arr.Length)
    // Zeros to the right of the first zero
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
    // The final array is a permutation of the original one
    ensures multiset(arr[..]) == multiset(old(arr[..]))
    // Relative order of non-zero elements is preserved
    ensures forall n, m /* on old array */:: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
            exists k, l /* on new array */:: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
    //ensures IsOrderPreserved(arr[..], old(arr[..]))
    // Number of zeros is preserved
// </vc-spec>
// <vc-code>
{
    var slow := 0;
    var a_orig := arr[..]; // Capture initial state for postcondition proofs

    for fast := 0 to arr.Length - 1
        invariant 0 <= slow <= fast + 1 <= arr.Length
        invariant forall i :: 0 <= i < slow ==> arr[i] != 0
        invariant forall i :: slow <= i <= fast ==> arr[i] == 0
        invariant multiset(arr[..]) == multiset(a_orig)
        invariant IsOrderPreserved(a_orig[..fast], arr[..fast], 0) // Tracks order for elements processed so far
        invariant (forall i :: 0 <= i < slow && arr[i] != 0 ==> (exists k :: 0 <= k < fast && a_orig[k] == arr[i]))
        invariant (forall i :: 0 <= i < slow && a_orig[i] != 0 ==> (exists k :: 0 <= k < slow && arr[k] == a_orig[i]))
        invariant (forall i :: slow <= i < arr.Length && arr[i] == 0 ==> (exists k :: 0 <= k < arr.Length && a_orig[k] == 0))
    {
        if arr[fast] != 0 {
            if slow != fast {
                var temp := arr[fast];
                arr[fast] := arr[slow];
                arr[slow] := temp;
            }
            slow := slow + 1;
        }
    }

    assert forall i :: 0 <= i < slow ==> arr[i] != 0;
    assert forall i :: slow <= i < arr.Length ==> arr[i] == 0;
    assert (forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0);

    assert IsOrderPreserved(a_orig, arr[..], 0);
}
// </vc-code>

