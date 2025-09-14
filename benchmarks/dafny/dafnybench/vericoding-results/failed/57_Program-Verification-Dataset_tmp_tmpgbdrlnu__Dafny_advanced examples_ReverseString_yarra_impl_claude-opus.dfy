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
  outarr := new char[arr.Length];
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant outarr.Length == arr.Length
    invariant forall k :: 0 <= k < i ==> outarr[k] == arr[arr.Length - 1 - k]
  {
    outarr[i] := arr[arr.Length - 1 - i];
    i := i + 1;
  }
}
// </vc-code>

