// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provide distinct-character counting function */
function DistinctCount(s: string): int {
  |set c: char | c in s|
}
// </vc-helpers>

// <vc-spec>
method find_max(strings : seq<string>) returns (s : string)

    requires |strings| > 0

    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): linear scan to find string with max distinct chars and prove postconditions */
  var i := 1;
  var best := 0;
  while i < |strings|
    invariant 1 <= i <= |strings|
    invariant 0 <= best < i
    invariant forall j:int :: 0 <= j < i ==> DistinctCount(strings[best]) >= DistinctCount(strings[j])
    decreases |strings| - i
  {
    if DistinctCount(strings[i]) > DistinctCount(strings[best]) {
      best := i;
    }
    i := i + 1;
  }
  s := strings[best];
  assert 0 <= best < |strings|;
  assert forall j:int :: 0 <= j < |strings| ==> DistinctCount(s) >= DistinctCount(strings[j]);
  assert exists k:int :: k == best && 0 <= k < |strings| && strings[k] == s;
}
// </vc-code>
