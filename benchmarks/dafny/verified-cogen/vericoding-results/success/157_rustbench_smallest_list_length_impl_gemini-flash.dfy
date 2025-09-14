// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function GetLength(a: array<int>): int { a.Length }
// </vc-helpers>

// <vc-spec>
method SmallestListLength(lists: array<array<int>>) returns (result: int)
    requires lists.Length > 0
    ensures exists i :: 0 <= i < lists.Length && result == lists[i].Length
    ensures forall i :: 0 <= i < lists.Length ==> result <= lists[i].Length
// </vc-spec>
// <vc-code>
{
    result := lists[0].Length;
    var i := 1;
    while i < lists.Length
        invariant 1 <= i <= lists.Length
        invariant exists k :: 0 <= k < i && result == lists[k].Length
        invariant forall k :: 0 <= k < i ==> result <= lists[k].Length
    {
        if lists[i].Length < result {
            result := lists[i].Length;
        }
        i := i + 1;
    }
}
// </vc-code>
