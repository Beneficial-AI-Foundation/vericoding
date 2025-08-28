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
lemma ReverseProperty(arr: array<char>, outarr: array<char>)
  requires arr.Length == outarr.Length
  requires forall k :: 0 <= k < arr.Length ==> outarr[k] == arr[arr.Length - 1 - k]
  ensures reversed(arr, outarr)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method yarra(arr : array<char>) returns (outarr : array<char>)
requires arr != null && arr.Length > 0
ensures outarr != null && arr.Length == outarr.Length && reversed(arr,outarr)
// </vc-spec>
// </vc-spec>

// <vc-code>
method ReverseString(arr: array<char>) returns (outarr: array<char>)
  requires arr.Length > 0
  ensures arr.Length == outarr.Length && reversed(arr, outarr)
{
  outarr := new char[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> outarr[k] == arr[arr.Length - 1 - k]
  {
    outarr[i] := arr[arr.Length - 1 - i];
    i := i + 1;
  }
  ReverseProperty(arr, outarr);
}
// </vc-code>
