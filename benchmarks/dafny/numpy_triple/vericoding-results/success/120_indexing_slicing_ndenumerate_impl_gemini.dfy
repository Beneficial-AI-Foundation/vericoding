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

// </vc-helpers>

// <vc-spec>
method ndenumerate(arr: array<real>) returns (result: seq<(int, real)>)
  ensures |result| == arr.Length
  ensures forall i :: 0 <= i < arr.Length ==> result[i] == (i, arr[i])
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (j, arr[j])
  {
    result := result + [(i, arr[i])];
    i := i + 1;
  }
}
// </vc-code>
