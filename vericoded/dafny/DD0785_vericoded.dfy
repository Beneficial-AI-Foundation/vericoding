

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
// </vc-spec>
// <vc-code>
{
    if |l| == 0 {
        return l;
    }
    
    r := [];
    var i := 0;
    
    while i < |l|
        invariant 0 <= i <= |l|
        invariant |r| == i
        invariant forall j :: 0 <= j < i ==> r[j] == l[(j - n + |l|) % |l|]
    {
        var sourceIndex := (i - n + |l|) % |l|;
        r := r + [l[sourceIndex]];
        i := i + 1;
    }
}
// </vc-code>

