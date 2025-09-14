// <vc-preamble>
function RotationSplit(len: int, n: int): int
    requires len > 0
{
    len - (n % len)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no helpers needed */
// </vc-helpers>

// <vc-spec>
method RotateRight(list: array<int>, n: int) returns (new_list: array<int>)
    requires list.Length > 0
    ensures new_list.Length == list.Length
    ensures fresh(new_list)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Corrected split_point calculation and loop bounds for array copying */
{
    var len := list.Length;
    var effective_n := n % len;
    var split_point := len - effective_n;

    new_list := new int[len];

    var i := 0;
    while i < effective_n
        invariant 0 <= i <= effective_n
        invariant forall k :: 0 <= k < i ==> new_list[k] == list[split_point + k]
        decreases effective_n - i
    {
        new_list[i] := list[split_point + i];
        i := i + 1;
    }

    var j := 0;
    while j < split_point
        invariant 0 <= j <= split_point
        invariant forall k :: 0 <= k < effective_n ==> new_list[k] == list[split_point + k]
        invariant forall k :: 0 <= k < j ==> new_list[effective_n + k] == list[k]
        decreases split_point - j
    {
        new_list[effective_n + j] := list[j];
        j := j + 1;
    }
}
// </vc-code>
