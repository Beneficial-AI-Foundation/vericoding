// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function RotatedIndex(i: int, n: nat, len: int): int
    requires 0 <= i < len
    requires len > 0
    ensures 0 <= RotatedIndex(i, n, len) < len
{
    ((i - n + len) % len)
}
// </vc-helpers>

// <vc-spec>
method RotateRight(l: array<int>, n: nat) returns (result: array<int>)
    ensures
        result.Length == l.Length &&
        (l.Length == 0 || forall i :: 0 <= i < l.Length ==> 
            var len := l.Length;
            var rotatedIndex := ((i - n + len) % len);
            result[i] == l[rotatedIndex])
// </vc-spec>
// <vc-code>
{
    if l.Length == 0 {
        result := new int[0];
    } else {
        result := new int[l.Length];
        for i := 0 to l.Length
            invariant 0 <= i <= l.Length
            invariant forall j :: 0 <= j < i ==> result[j] == l[RotatedIndex(j, n, l.Length)]
        {
            if i < l.Length {
                result[i] := l[RotatedIndex(i, n, l.Length)];
            }
        }
    }
}
// </vc-code>
