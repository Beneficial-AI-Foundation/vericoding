predicate ValidInput(arr: seq<int>) {
    true // No specific constraints on input beyond being a sequence of integers
}

function DistinctNonZeroCount(arr: seq<int>): int {
    |set x | x in arr && x != 0|
}

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result >= 0
    ensures result <= |arr|
    ensures result == DistinctNonZeroCount(arr)
// </vc-spec>
// <vc-code>
var count := 0;
  var found := set{};
  assert count <= |arr|;
  for i := 0 to |arr|
    invariant 0 <= i <= |arr|
    invariant count <= i <= |arr|
    invariant |found| == count
    invariant found == set x | x in arr[..i] && x != 0
    invariant count >= 0
  {
    if arr[i] != 0 && !(arr[i] in found) {
      count := count + 1;
      found := found + {arr[i]};
    }
  }
  result := count;
// </vc-code>

