// <vc-preamble>
function RotationSplit(len: int, n: int): int
    requires len > 0
{
    len - (n % len)
}
// </vc-preamble>

// <vc-helpers>
function EffectiveRotation(len: int, n: int): int
    requires len > 0
{
    n % len
}

function SourceIndex(len: int, destIndex: int, rot: int): int
    requires len > 0
    requires 0 <= destIndex < len
    requires 0 <= rot < len
{
    (destIndex - rot + len) % len
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
    var len := list.Length;
    var rot := EffectiveRotation(len, n);
    new_list := new int[len];
    
    var i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant forall j :: 0 <= j < i ==> new_list[j] == list[SourceIndex(len, j, rot)]
    {
        new_list[i] := list[SourceIndex(len, i, rot)];
        i := i + 1;
    }
}
// </vc-code>
