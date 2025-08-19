//IMPL
method FindPositionOfElement(a:array<int>,Element:nat,n1:nat,s1:seq<int>) returns (Position:int,Count:nat)
    requires n1 == |s1| && 0 <= n1 <= a.Length
    requires forall i:: 0<= i < |s1| ==> a[i] == s1[i]
    ensures Position == -1 || Position >= 1
    ensures |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element
{
    Position := -1;
    Count := 0;
    
    var i := 0;
    while i < |s1|
        invariant 0 <= i <= |s1|
        invariant Position == -1 || Position >= 1
        invariant Position >= 1 ==> exists j:: 0 <= j < i && s1[j] == Element
    {
        if s1[i] == Element {
            Position := i + 1;  // Convert to 1-based indexing
            Count := Count + 1;
            return;
        }
        i := i + 1;
    }
}