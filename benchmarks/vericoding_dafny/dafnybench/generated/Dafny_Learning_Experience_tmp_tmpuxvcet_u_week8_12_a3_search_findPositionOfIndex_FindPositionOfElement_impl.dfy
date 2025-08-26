// The method should return the 1-based position of the element if found, or -1 if not found. It should also return a count (though the spec doesn't specify what this count represents, I'll assume it's the number of occurrences).

// <vc-helpers>
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
  
  var i := 0;
  while i < n1
    invariant 0 <= i <= n1
    invariant Position == -1 || Position >= 1
    invariant Position >= 1 ==> exists j:: 0 <= j < i && s1[j] == Element
    invariant Count >= 0
  {
    if s1[i] == Element {
      if Position == -1 {
        Position := i + 1; // Convert to 1-based indexing
      }
      Count := Count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>