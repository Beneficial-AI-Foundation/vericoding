

// <vc-helpers>
predicate PartitionUpTo(a: array<int>, low: int, mid: int, high: int)
  requires 0 <= low <= mid <= high + 1 <= a.Length
  reads a
{
  (forall x :: 0 <= x < low ==> a[x] < 0)
  && (forall x :: low <= x < mid ==> a[x] == 0)
  && (forall x :: high < x < a.Length ==> a[x] > 0)
}
// </vc-helpers>

// <vc-spec>
method Partition(a: array<int>) returns (lo: int, hi: int)
  modifies a
  ensures 0 <= lo <= hi <= a.Length
  ensures forall x | 0 <= x < lo :: a[x] < 0
  ensures forall x | lo <= x < hi :: a[x] == 0
  ensures forall x | hi <= x < a.Length :: a[x] > 0
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var mid := 0;
    var high := a.Length - 1;
    while mid <= high
        invariant 0 <= low <= mid <= high + 1 <= a.Length
        invariant PartitionUpTo(a, low, mid, high)
        decreases high - mid + 1
    {
        if a[mid] < 0 {
            a[low], a[mid] := a[mid], a[low];
            low := low + 1;
            mid := mid + 1;
        } else if a[mid] == 0 {
            mid := mid + 1;
        } else {
            a[mid], a[high] := a[high], a[mid];
            high := high - 1;
        }
    }
    lo := low;
    hi := high + 1;
}
// </vc-code>

