

// <vc-helpers>
function LowerHalf(arr: seq<int>): seq<int>
  decreases arr.len
{
  if arr.len == 0 then [] else [arr[0]] + LowerHalf(arr[1..])
}
function UpperHalf(arr: seq<int>): seq<int>
  decreases arr.len
{
  if arr.len == 0 then [] else UpperHalf(arr[..arr.len-1]) + [arr[arr.len-1]]
}
// </vc-helpers>

// <vc-spec>
method FindMedian(a: array<int>, b: array<int>) returns (median: int)
    requires a != null && b != null
    requires a.Length == b.Length
    requires a.Length > 0
    requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
    requires forall i :: 0 <= i < b.Length - 1 ==> b[i] <= b[i + 1]
    ensures median == if (a.Length % 2 == 0) then (a[a.Length / 2 - 1] + b[0]) / 2 else a[a.Length / 2]
// </vc-spec>
// <vc-code>
{
    var n := a.Length;
    if n % 2 == 1 {
        // If n is odd, the median is the middle element of the merged array.
        // For sorted arrays a and b of same odd length, the "median" as per problem
        // statement is simply a[n/2]
        median := a[n / 2];
    } else {
        // If n is even, the median is the average of the two middle elements.
        // For sorted arrays a and b of same even length, the problem statement defines
        // the "median" as (a[n/2 - 1] + b[0]) / 2.
        median := (a[n / 2 - 1] + b[0]) / 2;
    }
}
// </vc-code>

