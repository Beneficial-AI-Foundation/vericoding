// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): count distinct characters in a string */
function distinct_count(s: string): nat {
  |set c | c in s|
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
  /* code modified by LLM (iteration 2): find index with maximum distinct char count */
  var bestIdx := 0;
  var bestCount := distinct_count(strings[0]);
  var i := 1;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant 0 <= bestIdx < |strings|
    invariant bestCount == distinct_count(strings[bestIdx])
    invariant forall j :: 0 <= j < i ==> bestCount >= distinct_count(strings[j])
  {
    var cnt := distinct_count(strings[i]);
    if cnt > bestCount {
      bestIdx := i;
      bestCount := cnt;
    }
    i := i + 1;
  }
  s := strings[bestIdx];
}
// </vc-code>
