predicate ValidInput(arr: seq<int>) {
    true // No specific constraints on input beyond being a sequence of integers
}

function DistinctNonZeroCount(arr: seq<int>): int {
    |set x | x in arr && x != 0|
}

// <vc-helpers>
// Added no helper lemmas; implementation uses a simple loop with precise invariants.
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
  var i := 0;
  var seen: set<int> := {};
  var cnt := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant seen == {x | exists k :: 0 <= k < i && arr[k] == x && x != 0}
    invariant cnt == |seen|
    invariant cnt <= i
  {
    var a := arr[i];
    if a != 0 && !(a in seen) {
      seen := seen + {a};
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  result := cnt;
}
// </vc-code>

