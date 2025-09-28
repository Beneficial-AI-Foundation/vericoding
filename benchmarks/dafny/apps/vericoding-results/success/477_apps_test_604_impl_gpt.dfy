predicate ValidInput(arr: seq<int>) {
    true // No specific constraints on input beyond being a sequence of integers
}

function DistinctNonZeroCount(arr: seq<int>): int {
    |set x | x in arr && x != 0|
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result >= 0
    ensures result <= |arr|
    ensures result == DistinctNonZeroCount(arr)
// </vc-spec>
// <vc-code>
{
  var seen: set<int> := {};
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant seen == set x: int | x in arr[..i] && x != 0
    invariant |seen| <= i
    decreases |arr| - i
  {
    i := i + 1;
    if arr[i - 1] != 0 {
      seen := seen + {arr[i - 1]};
    }
  }
  assert i == |arr|;
  assert arr[..i] == arr;
  assert (set x: int | x in arr[..i] && x != 0) == (set x: int | x in arr && x != 0);
  result := |seen|;
}
// </vc-code>

