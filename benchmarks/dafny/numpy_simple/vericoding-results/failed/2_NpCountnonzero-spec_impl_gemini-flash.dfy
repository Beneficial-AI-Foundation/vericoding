// <vc-preamble>
function nonzero_helper(arr: seq<real>): nat 
    decreases |arr|
{
    if |arr| == 0 then
        0
    else
        var rest_count := nonzero_helper(arr[1..]);
        if arr[0] == 0.0 then
            rest_count
        else
            rest_count + 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method nonzero(arr: array<real>) returns (result: int)
    ensures 
        result <= arr.Length &&
        result == nonzero_helper(arr[..]) &&
        (arr.Length > 0 && arr[0] == 0.0 ==> 
            nonzero_helper(arr[1..]) == if result > 0 then result - 1 else 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed errors related to postcondition when arr.Length is greater than 0 by using if/else for the third ensures clause. */
  if arr.Length == 0 {
    return 0;
  }

  var count := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant count == nonzero_helper(arr[..i])
    decreases arr.Length - i
  {
    if arr[i] != 0.0 {
      count := count + 1;
    }
    i := i + 1;
  }
  result := count;

  // To prove the third ensures clause manually:
  // (arr.Length > 0 && arr[0] == 0.0 ==> 
  //      nonzero_helper(arr[1..]) == if result > 0 then result - 1 else 0)
  if arr.Length > 0 && arr[0] == 0.0 {
      var expected_rest_count := nonzero_helper(arr[1..]);
      var computed_val := if result > 0 then result - 1 else 0;
      assert expected_rest_count == computed_val;
  }

  assert result == nonzero_helper(arr[..]);
}
// </vc-code>
