// <vc-helpers>
lemma ModuloProperties(a: int, b: int)
    requires b > 0
    ensures (a % b + b) % b == a % b
{
}

lemma RotationIndexing(i: int, n: int, len: int)
    requires len > 0
    requires 0 <= i < len
    requires n >= 0
    ensures 0 <= (i + len - n % len) % len < len
{
    var shift := n % len;
    var newIndex := (i + len - shift) % len;
    assert 0 <= newIndex < len;
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if |l| == 0 {
        return [];
    }
    
    var effectiveN := n % |l|;
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
