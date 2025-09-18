// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method unique_product(arr: array<int>) returns (result: int)
    ensures
        /* Product of all unique integers in the array */
        true /* Placeholder for actual postcondition */
// </vc-spec>
// <vc-code>
{
  var s: set<int> := {};
  var prod: int := 1;
  for i := 0 to arr.Length {
    if arr[i] !in s {
      s := s + {arr[i]};
      prod := prod * arr[i];
    }
  }
  result := prod;
}
// </vc-code>
