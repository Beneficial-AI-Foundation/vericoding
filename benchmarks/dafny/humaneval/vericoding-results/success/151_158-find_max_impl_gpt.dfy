// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function DistinctCount(s: string): nat { |set c | c in s| }
// </vc-helpers>

// <vc-spec>
method find_max(strings : seq<string>) returns (s : string)

    requires |strings| > 0

    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
// </vc-spec>
// <vc-code>
{
  var i := 1;
  var bestIndex := 0;
  var best := strings[0];

  while i < |strings|
    invariant 1 <= i <= |strings|
    invariant 0 <= bestIndex < i
    invariant best == strings[bestIndex]
    invariant forall j :: 0 <= j < i ==> DistinctCount(best) >= DistinctCount(strings[j])
    decreases |strings| - i
  {
    if DistinctCount(strings[i]) > DistinctCount(best) {
      best := strings[i];
      bestIndex := i;
    }
    i := i + 1;
  }

  s := strings[bestIndex];
  assert s in strings;
}
// </vc-code>
