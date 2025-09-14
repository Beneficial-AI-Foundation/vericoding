

// <vc-helpers>
method Swap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}
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
    invariant 0 <= i <= (a.Length / 2) + (a.Length % 2)
    invariant a.Length / 2 <= j < a.Length
    invariant i <= j + 1
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[(a.Length - 1) - k])
    invariant forall k :: j < k < a.Length ==> a[k] == old(a[(a.Length - 1) - k])
    invariant i + j == a.Length - 1
  {
    Swap(a, i, j);
    i := i + 1;
    j := j - 1;
  }
}
// </vc-code>

