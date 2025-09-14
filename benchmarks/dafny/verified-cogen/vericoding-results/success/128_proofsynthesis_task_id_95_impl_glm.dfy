// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Renamed helper function to avoid conflict with return variable */
function MinInt(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method SmallestListLength(list: array<array<int>>) returns (min: int)
    requires list.Length > 0
    ensures min >= 0
    ensures forall i :: 0 <= i < list.Length ==> min <= list[i].Length
    ensures exists i :: 0 <= i < list.Length && min == list[i].Length
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Updated calls to use MinInt instead of min */
{
    var smallest := list[0].Length;
    var i := 1;
    while i < list.Length
        invariant 0 <= i <= list.Length
        invariant forall j :: 0 <= j < i ==> smallest <= list[j].Length
        invariant exists j :: 0 <= j < i && smallest == list[j].Length
    {
        smallest := MinInt(smallest, list[i].Length);
        i := i + 1;
    }
    min := smallest;
}
// </vc-code>
