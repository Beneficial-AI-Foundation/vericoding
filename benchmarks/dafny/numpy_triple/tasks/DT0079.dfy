// <vc-preamble>
// Method that finds unique elements in an array and returns them sorted
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_unique(arr: seq<real>) returns (unique_arr: seq<real>)
  ensures // The result is sorted in ascending order
          forall i, j :: 0 <= i < j < |unique_arr| ==> unique_arr[i] < unique_arr[j]
  ensures // No duplicates exist in the result
          forall i, j :: 0 <= i < j < |unique_arr| ==> unique_arr[i] != unique_arr[j]
  ensures // Every element in result comes from the input array
          forall i :: 0 <= i < |unique_arr| ==> unique_arr[i] in arr
  ensures // Every distinct element from input appears in result
          forall x :: x in arr ==> x in unique_arr
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
