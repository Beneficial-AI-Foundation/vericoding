

// <vc-helpers>
function Search(a: array<int>, low: int, high: int): int
   requires a != null
   requires 0 <= low <= high <= a.Length
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures -1 <= Search(a, low, high) < high
   ensures Search(a, low, high) < 0 ==> forall i :: low <= i < high ==> a[i] != 0
   ensures 0 <= Search(a, low, high) ==> a[Search(a, low, high)] == 0
{
   if low == high then -1
   else
     var mid := (low + high) / 2;
     if a[mid] == 0 then mid
     else if a[mid] <= mid then Search(a, low, mid)
     else Search(a, mid + 1, high)
}
// </vc-helpers>
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
   return Search(a, 0, a.Length);
}
// </vc-code>

