// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
    var len := l.Length;
    result := new int[len];
    if len > 0 {
        var i := 0;
        while i < len
            invariant 0 <= i <= len
            invariant forall j :: 0 <= j < i ==> result[j] == l[((j - n + len) % len)]
        {
            var rotatedIndex := (i - n + len) % len;
            result[i] := l[rotatedIndex];
            i := i + 1;
        }
    }
}
// </vc-code>
