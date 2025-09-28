// <vc-preamble>
function RotationSplit(len: int, n: int): int
    requires len > 0
{
    len - (n % len)
}
// </vc-preamble>

// <vc-helpers>
predicate ValidRotation(original: array<int>, rotated: array<int>, n: int)
    reads original, rotated
{
    original.Length == rotated.Length &&
    original.Length > 0 &&
    forall i :: 0 <= i < original.Length ==> 
        rotated[i] == original[(i + RotationSplit(original.Length, n)) % original.Length]
}
// </vc-helpers>

// <vc-spec>
method RotateRight(list: array<int>, n: int) returns (new_list: array<int>)
    requires list.Length > 0
    ensures new_list.Length == list.Length
    ensures fresh(new_list)
// </vc-spec>
// <vc-code>
{
    new_list := new int[list.Length];
    var split := RotationSplit(list.Length, n);
    
    var i := 0;
    while i < list.Length
        invariant 0 <= i <= list.Length
        invariant forall j :: 0 <= j < i ==> new_list[j] == list[(j + split) % list.Length]
    {
        new_list[i] := list[(i + split) % list.Length];
        i := i + 1;
    }
}
// </vc-code>
