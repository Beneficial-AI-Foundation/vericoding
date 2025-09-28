// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsOddAtOddIndex(arr: array<int>) returns (result: bool)
    ensures result == forall i :: 0 <= i < arr.Length ==> ((i % 2) == (arr[i] % 2))
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> ((j % 2) == (arr[j] % 2))
    {
        if (i % 2) != (arr[i] % 2)
        {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>
