predicate ValidInput(arr: seq<int>) {
    true // No specific constraints on input beyond being a sequence of integers
}

function DistinctNonZeroCount(arr: seq<int>): int {
    |set x | x in arr && x != 0|
}

// <vc-helpers>
lemma CountLemma(arr: seq<int>, s: set<int>)
    decreases |arr|
    ensures |set x | x in arr && x != 0| == |s| + |set x | x in arr && x != 0 && x !in s|
{
    if |arr| == 0 {
    } else {
        var x := arr[0];
        var rest := arr[1..];
        if x == 0 || x in s {
            CountLemma(rest, s);
        } else {
            CountLemma(rest, s + {x});
        }
    }
}
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
  if |arr| == 0 {
    result := 0;
    return;
  }
  
  var seen: set<int> := {};
  result := 0;
  
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant seen == set x:int | x in arr[0..i] && x != 0 
    invariant result == |seen|
    invariant result <= |arr|
  {
    var x := arr[i];
    if x != 0 && x !in seen {
      seen := seen + {x};
      result := result + 1;
    }
    i := i + 1;
  }
  
  CountLemma(arr, {});
}
// </vc-code>

