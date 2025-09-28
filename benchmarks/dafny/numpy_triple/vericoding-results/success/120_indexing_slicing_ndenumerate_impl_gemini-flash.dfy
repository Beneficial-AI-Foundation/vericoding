// <vc-preamble>
/*
 * Dafny specification for numpy.ndenumerate: Multidimensional index iterator
 * that yields pairs of array coordinates and values. For each position in the
 * input array, returns a tuple containing the index and the corresponding value.
 */

// Method that enumerates through an array, providing pairs of (index, value)
// for each element in the input array
// </vc-preamble>

// <vc-helpers>
function Tuple(index: int, value: real): (int, real) { (index, value) }
// </vc-helpers>

// <vc-spec>
method ndenumerate(arr: array<real>) returns (result: seq<(int, real)>)
  ensures |result| == arr.Length
  ensures forall i :: 0 <= i < arr.Length ==> result[i] == (i, arr[i])
// </vc-spec>
// <vc-code>
{
  var tempResult: seq<(int, real)> := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant |tempResult| == i
    invariant forall k :: 0 <= k < i ==> tempResult[k] == (k, arr[k])
  {
    tempResult := tempResult + [(i, arr[i])];
    i := i + 1;
  }
  result := tempResult;
}
// </vc-code>
