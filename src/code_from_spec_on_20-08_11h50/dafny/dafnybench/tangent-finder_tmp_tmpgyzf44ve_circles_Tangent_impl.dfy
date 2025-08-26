// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Tangent(r: array<int>, x: array<int>) returns (b: bool)
    requires forall i, j :: 0 <= i <= j < x.Length ==> x[i] <= x[j] // values in x will be in ascending order or empty
    requires forall i, j :: (0 <= i < r.Length && 0 <= j < x.Length) ==> (r[i] >= 0 && x[j] >= 0)       // x and r will contain no negative values
    ensures !b ==> forall i, j :: 0 <= i< r.Length && 0 <= j < x.Length ==> r[i] != x[j]   
    ensures b ==> exists i, j :: 0 <= i< r.Length && 0 <= j < x.Length && r[i] == x[j]
// </vc-spec>
// <vc-code>
{
    b := false;
    
    var i := 0;
    while i < r.Length
        invariant 0 <= i <= r.Length
        invariant !b ==> forall k, j :: 0 <= k < i && 0 <= j < x.Length ==> r[k] != x[j]
        invariant b ==> exists k, j :: 0 <= k < r.Length && 0 <= j < x.Length && r[k] == x[j]
    {
        var j := 0;
        while j < x.Length
            invariant 0 <= j <= x.Length
            invariant !b ==> forall l :: 0 <= l < j ==> r[i] != x[l]
            invariant b ==> exists k, l :: 0 <= k < r.Length && 0 <= l < x.Length && r[k] == x[l]
        {
            if r[i] == x[j] {
                b := true;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>