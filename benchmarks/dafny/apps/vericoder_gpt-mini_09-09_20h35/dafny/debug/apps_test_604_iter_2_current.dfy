predicate ValidInput(arr: seq<int>) {
    true // No specific constraints on input beyond being a sequence of integers
}

function DistinctNonZeroCount(arr: seq<int>): int {
    |set x | x in arr && x != 0|
}

// <vc-helpers>
// No helper lemmas required for this implementation.
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
  var s: set<int> := {};
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant s == set x | exists j :: 0 <= j < i && arr[j] == x && x != 0
    invariant |s| <= i
  {
    if arr[i] != 0 {
      s := s + {arr[i]};
    }
    i := i + 1;
  }
  assert s == (set x | x in arr && x != 0);
  result := |s|;
}
// </vc-code>

