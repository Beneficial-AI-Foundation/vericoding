

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SplitArray(arr: array<int>, L: int) returns (firstPart: seq<int>, secondPart: seq<int>)
    requires 0 <= L <= arr.Length
    ensures |firstPart| == L
    ensures |secondPart| == arr.Length - L
    ensures firstPart + secondPart == arr[..]
// </vc-spec>
// <vc-code>
{
    var first: seq<int> := [];
    var second: seq<int> := [];

    var i := 0;
    while i < L
        invariant 0 <= i <= L
        invariant first == arr[..i]
        invariant second == []
        invariant |first| == i
    {
        first := first + [arr[i]];
        i := i + 1;
    }
    
    var j := L;
    while j < arr.Length
        invariant L <= j <= arr.Length
        invariant first == arr[..L]
        invariant second == arr[L..j]
        invariant |second| == j - L
    {
        second := second + [arr[j]];
        j := j + 1;
    }

    firstPart := first;
    secondPart := second;
}
// </vc-code>

