// http://verifythus.cost-ic0701.org/common-example/arraymax-in-dafny

// <vc-helpers>
predator
// </vc-helpers>

// <vc-spec>
method max(a:array<int>) returns(max:int)
    requires a != null;
    ensures forall j :: j >= 0 && j < a.Length ==> max >= a[j]; //max is larger then anything in the array
    ensures a.Length > 0 ==> exists j :: j >= 0 && j < a.Length && max == a[j]; //max is an element in the array
// </vc-spec>
// <vc-code>
{
  if a.Length == 0 {
    return 0;
  }
  var currentMax := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= i && i <= a.Length
    invariant forall j :: 0 <= j && j < i ==> currentMax >= a[j]
    invariant exists j :: 0 <= j && j < i && currentMax == a[j]
  {
    if a[i] > currentMax {
      currentMax := a[i];
    }
    i := i + 1;
  }
  return currentMax;
}
// </vc-code>

