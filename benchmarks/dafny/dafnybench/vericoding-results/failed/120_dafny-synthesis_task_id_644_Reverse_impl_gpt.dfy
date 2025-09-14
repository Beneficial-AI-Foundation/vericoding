

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Reverse(a: array<int>)
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var j := a.Length - 1;
  while i < j
    invariant 0 <= i <= a.Length
    invariant -1 <= j < a.Length
    invariant i + j == a.Length - 1
    invariant forall t :: 0 <= t < i ==> a[t] == old(a[(a.Length - 1) - t])
    invariant forall t :: j < t < a.Length ==> a[t] == old(a[(a.Length - 1) - t])
    invariant forall t :: i <= t <= j ==> a[t] == old(a[t])
    decreases j - i
  {
    var tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
    i := i + 1;
    j := j - 1;
  }
}
// </vc-code>

