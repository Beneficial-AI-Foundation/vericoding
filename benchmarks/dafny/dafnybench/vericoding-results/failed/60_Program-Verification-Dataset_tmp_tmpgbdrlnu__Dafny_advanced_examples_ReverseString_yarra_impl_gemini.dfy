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
  /* code modified by LLM (iteration 5): corrected 'for' loop syntax from '..' to 'to' */
  outarr := new char[arr.Length];
  for i := 0 to arr.Length
    invariant outarr.Length == arr.Length
    invariant forall k :: 0 <= k < i ==> outarr[k] == arr[arr.Length - 1 - k]
    invariant outarr.fresh(outarr.Length)
  {
    outarr[i] := arr[arr.Length - 1 - i];
  }
}
// </vc-code>
