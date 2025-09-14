

// <vc-helpers>
lemma ElementFoundImpliesExists(s: seq<int>, element: int, pos: int)
    requires 0 <= pos < |s|
    requires s[pos] == element
    ensures exists i :: 0 <= i < |s| && s[i] == element
{
    // The witness is pos itself
}
// </vc-helpers>

// <vc-spec>
method FindPositionOfElement(a:array<int>,Element:nat,n1:nat,s1:seq<int>) returns (Position:int,Count:nat)
        requires n1 == |s1| && 0 <= n1 <= a.Length
        requires forall i:: 0<= i < |s1| ==> a[i] == s1[i]
        ensures Position == -1 || Position >= 1
        ensures |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element
// </vc-spec>
// <vc-code>
{
    Position := -1;
    Count := 0;
    
    if n1 == 0 {
        return;
    }
    
    var i := 0;
    while i < n1
        invariant 0 <= i <= n1
        invariant Position == -1 || Position >= 1
        invariant Position >= 1 ==> exists j :: 0 <= j < |s1| && s1[j] == Element
    {
        if a[i] == Element {
            Position := i + 1;
            ElementFoundImpliesExists(s1, Element, i);
            Count := Count + 1;
        } else {
            Count := Count + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

