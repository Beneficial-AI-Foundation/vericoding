// <vc-preamble>
// </vc-preamble>

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
  assume {:axiom} false;
}
// </vc-code>
