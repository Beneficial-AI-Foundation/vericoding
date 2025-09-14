

// <vc-helpers>
// Added a small helper lemma to assist with reasoning about the unchanged tail of the array.
// This lemma is trivial but can help Dafny's verifier with instantiation in some cases.
lemma UnchangedTailIsPreserved(oldA: seq<int>, a: array<int>, i: int, n: int)
  requires a.Length == |oldA|
  requires 0 <= i <= n <= a.Length
  requires forall j :: i <= j < n ==> a[j] == oldA[j]
  ensures forall j :: i <= j < n ==> a[j] == oldA[j]
{
  // trivial
}
// </vc-helpers>

// <vc-spec>
method ZapNegatives(a: array<int>) 
modifies a
ensures forall i :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 
                                            else a[i] == old(a[i])
ensures a.Length == old(a).Length
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  ghost var oldA := a[..];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a.Length == |oldA|
    invariant n == |oldA|
    invariant a.Length == n
    invariant forall j :: 0 <= j < i ==>
                if oldA[j] < 0 then a[j] == 0 else a[j] == oldA[j]
    invariant forall j :: i <= j < n ==> a[j] == oldA[j]
    decreases n - i
  {
    var v := oldA[i];
    if v < 0 {
      a[i] := 0;
    }
    i := i + 1;
  }
}
// </vc-code>

