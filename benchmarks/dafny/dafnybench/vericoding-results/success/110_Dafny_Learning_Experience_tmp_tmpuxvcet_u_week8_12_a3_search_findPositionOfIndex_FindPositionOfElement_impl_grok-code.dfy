

// <vc-helpers>
// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>
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
  var PositionLocal := -1;
  var CountLocal := 0;
  var i := 0;
  while i < n1
    invariant 0 <= i <= n1
    invariant PositionLocal == -1 || (1 <= PositionLocal <= i && PositionLocal >= 1)
    invariant PositionLocal == -1 ==> forall k :: 0 <= k < i ==> s1[k] != Element
    invariant PositionLocal == -1 || (PositionLocal >= 1 && s1[PositionLocal - 1] == Element && forall k :: 0 <= k < PositionLocal - 1 ==> s1[k] != Element)
    invariant CountLocal >= 0
  {
    if a[i] == Element {
      if PositionLocal == -1 {
        PositionLocal := i + 1;
      }
      CountLocal := CountLocal + 1;
    }
    i := i + 1;
  }
  Position := PositionLocal;
  Count := CountLocal;
}
// </vc-code>

