

// <vc-helpers>
// <vc-spec>
method FindZero(a: array?<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
// </vc-spec>
// </vc-helpers>

// <vc-spec>
method FindZero(a: array<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
// </vc-spec>
// <vc-code>
{
  index := -1;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant index == -1 || 0 <= index < i
    invariant index >= 0 ==> a[index] == 0
    invariant forall j | 0 <= j < i :: a[j] != 0
  {
    if a[i] == 0 {
      index := i;
      break;
    }
    i := i + 1;
  }
  if index >= 0 {
    // Ensures satisfied by invariant
  } else {
    // Ensures satisfied by invariant: forall i | 0 <= i < a.Length :: a[i] != 0
  }
}
// </vc-code>

