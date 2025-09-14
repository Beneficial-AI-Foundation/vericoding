

// <vc-helpers>
lemma ExistsNotForall(a: seq<int>, b: seq<int>)
    requires |a| == |b|
    ensures (exists i :: 0 <= i < |a| && a[i] <= b[i]) <==> !(forall i :: 0 <= i < |a| ==> a[i] > b[i])
{
    if exists i :: 0 <= i < |a| && a[i] <= b[i] {
        var j :| 0 <= j < |a| && a[j] <= b[j];
        assert !(forall i :: 0 <= i < |a| ==> a[i] > b[i]);
    }
    
    if !(forall i :: 0 <= i < |a| ==> a[i] > b[i]) {
        assert exists i :: 0 <= i < |a| && a[i] <= b[i];
    }
}
// </vc-helpers>

// <vc-spec>
method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
    requires |a| == |b|
    ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
    ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
// </vc-spec>
// <vc-code>
{
    result := true;
    var i := 0;
    
    while i < |a|
        invariant 0 <= i <= |a|
        invariant result <==> forall j :: 0 <= j < i ==> a[j] > b[j]
    {
        if a[i] <= b[i] {
            result := false;
            break;
        }
        i := i + 1;
    }
    
    ExistsNotForall(a, b);
}
// </vc-code>

