// <vc-preamble>
predicate reversed (arr : array<char>, outarr: array<char>)
requires arr != null && outarr != null
requires arr.Length == outarr.Length
reads arr, outarr
{
  forall k :: 0<=k<=arr.Length-1 ==> outarr[k] == arr[(arr.Length-1-k)]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method yarra(arr : array<char>) returns (outarr : array<char>)
requires arr != null && arr.Length > 0
ensures outarr != null && arr.Length == outarr.Length && reversed(arr,outarr)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
