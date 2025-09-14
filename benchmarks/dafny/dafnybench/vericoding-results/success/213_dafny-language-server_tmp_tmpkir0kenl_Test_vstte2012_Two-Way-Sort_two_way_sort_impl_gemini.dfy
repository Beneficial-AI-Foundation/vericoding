// <vc-preamble>
function multisets<T>(s: seq<T>): multiset<T>
{
    if |s| == 0 then multiset{} 
    else multiset{s[0]} + multiset(s[1..])
}

method swap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method two_way_sort(a: array<bool>)
  modifies a
  ensures forall m,n :: 0 <= m < n < a.Length ==> (!a[m] || a[n])
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := a.Length - 1;

  while low <= high
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant 0 <= low <= a.Length
    invariant -1 <= high < a.Length
    invariant forall k :: 0 <= k < low ==> !a[k]
    invariant forall k :: high < k < a.Length ==> a[k]
    decreases high - low
  {
    if low <= high && !a[low] {
      low := low + 1;
    } else if low <= high && a[high] {
      high := high - 1;
    } else {
      // Here we know a[low] is true and a[high] is false.
      // Since low <= high and the first two branches did not hold, it must be that low < high.
      swap(a, low, high);
      low := low + 1;
      high := high - 1;
    }
  }
}
// </vc-code>
