// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed problematic lemma and kept only necessary functions */
function IsOdd(x: int): bool { x % 2 != 0 }

function CountOddNumbers(arr: array<int>): int
    reads arr
{
    |set i | 0 <= i < arr.Length && arr[i] % 2 != 0|
}
// </vc-helpers>

// <vc-spec>
method FilterOddNumbers(arr: array<int>) returns (odd_list: seq<int>)
    ensures |odd_list| == |set i | 0 <= i < arr.Length && arr[i] % 2 != 0|
    ensures forall x :: x in odd_list ==> x % 2 != 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 != 0 ==> arr[i] in odd_list
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added ghost variable to track set cardinality */
    odd_list := [];
    var i := 0;
    ghost var odd_indices := {};
    
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall x :: x in odd_list ==> x % 2 != 0
        invariant forall j :: 0 <= j < i && arr[j] % 2 != 0 ==> arr[j] in odd_list
        invariant odd_indices == set j | 0 <= j < i && arr[j] % 2 != 0
        invariant |odd_list| == |odd_indices|
    {
        if arr[i] % 2 != 0 {
            odd_list := odd_list + [arr[i]];
            odd_indices := odd_indices + {i};
        }
        i := i + 1;
    }
}
// </vc-code>
