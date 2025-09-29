// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AnyValueExists(arr1: array<int>, arr2: array<int>) returns (result: bool)
    ensures result == exists k :: 0 <= k < arr1.Length && k in arr2[..]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed invariant to track if any index value up to i exists in arr2 */
  result := false;
  var i := 0;
  while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant result == (exists k :: 0 <= k < i && k in arr2[..])
  {
    if !result {
      var j := 0;
      var found := false;
      while j < arr2.Length
        invariant 0 <= j <= arr2.Length
        invariant found == (i in arr2[..j])
      {
        if arr2[j] == i {
          found := true;
        }
        j := j + 1;
      }
      assert found == (i in arr2[..]);
      if found {
        result := true;
      }
    }
    i := i + 1;
  }
}
// </vc-code>
