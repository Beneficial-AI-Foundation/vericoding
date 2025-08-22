//IMPL 
method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
    requires |a| == |b|
    ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
    ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
{
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall j :: 0 <= j < i ==> a[j] > b[j]
    {
        if a[i] <= b[i] {
            result := false;
            return;
        }
        i := i + 1;
    }
    result := true;
}