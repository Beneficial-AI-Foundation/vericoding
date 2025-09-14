// RUN: /compile:0

predicate reversed (arr : array<char>, outarr: array<char>)
requires arr != null && outarr != null
//requires 0<=k<=arr.Length-1
requires arr.Length == outarr.Length
reads arr, outarr
{
  forall k :: 0<=k<=arr.Length-1 ==> outarr[k] == arr[(arr.Length-1-k)]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method yarra(arr : array<char>) returns (outarr : array<char>)
requires arr != null && arr.Length > 0
ensures outarr != null && arr.Length == outarr.Length && reversed(arr,outarr)
// </vc-spec>
// <vc-code>
{
  var n := arr.Length;
  outarr := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant outarr.Length == n
    invariant forall k :: 0 <= k < i ==> outarr[k] == arr[n - 1 - k]
    decreases n - i
  {
    outarr[i] := arr[n - 1 - i];
    i := i + 1;
  }
  assert i == n;
  assert forall k :: 0 <= k < n ==> outarr[k] == arr[n - 1 - k];
  assert reversed(arr, outarr);
}
// </vc-code>

