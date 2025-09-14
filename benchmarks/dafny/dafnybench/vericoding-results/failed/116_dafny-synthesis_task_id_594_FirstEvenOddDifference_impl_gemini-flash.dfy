predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
function FindFirstEven(arr: array<int>): (index: int)
    requires arr.Length > 0
    requires exists i :: 0 <= i < arr.Length && IsEven(arr[i])
    ensures 0 <= index < arr.Length
    ensures IsEven(arr[index])
    ensures forall k :: 0 <= k < index ==> IsOdd(arr[k])
{
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall k :: 0 <= k < i ==> IsOdd(arr[k])
        decreases arr.Length - i
    {
        if IsEven(arr[i]) then
            return i;
        i := i + 1;
    }
    // This part is unreachable due to the requires clause
    return 0; // Returning a default value, though unreachable
}

function FindFirstOdd(arr: array<int>): (index: int)
    requires arr.Length > 0
    requires exists i :: 0 <= i < arr.Length && IsOdd(arr[i])
    ensures 0 <= index < arr.Length
    ensures IsOdd(arr[index])
    ensures forall k :: 0 <= k < index ==> IsEven(arr[k])
{
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall k :: 0 <= k < i ==> IsEven(arr[k])
        decreases arr.Length - i
    {
        if IsOdd(arr[i]) then
            return i;
        i := i + 1;
    }
    // This part is unreachable due to the requires clause
    return 0; // Returning a default value, though unreachable
}
// </vc-helpers>

// <vc-spec>
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
    requires a.Length >= 2
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
// </vc-spec>
// <vc-code>
{
    var even_idx := FindFirstEven(a);
    var odd_idx := FindFirstOdd(a);
    return a[even_idx] - a[odd_idx];
}
// </vc-code>

