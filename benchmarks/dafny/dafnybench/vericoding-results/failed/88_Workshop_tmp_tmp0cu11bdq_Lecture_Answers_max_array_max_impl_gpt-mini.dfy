// http://verifythus.cost-ic0701.org/common-example/arraymax-in-dafny

// <vc-helpers>
// No helper code required for this example
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
    return 0
  }
  var i := 1
  max := a[0]
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> max >= a[k]
    invariant exists k :: 0 <= k < i && max == a[k]
    decreases a.Length - i
  {
    if a[i] > max {
      max := a[i]
    }
    i := i + 1
  }
  return
}
// </vc-code>

