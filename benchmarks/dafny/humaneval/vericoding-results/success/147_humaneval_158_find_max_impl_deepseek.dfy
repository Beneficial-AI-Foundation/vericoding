// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed function signature and return type */
function count_unique_chars(s: string): int {
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
  /* code modified by LLM (iteration 4): Fixed loop index bounds in invariant */
  var idx := 0;
  var maxUnique := count_unique_chars(strings[0]);
  var i := 1;
  while i < |strings|
      invariant 1 <= i <= |strings|
      invariant 0 <= idx < |strings|
      invariant maxUnique == count_unique_chars(strings[idx])
      invariant forall k :: 0 <= k < i ==> maxUnique >= count_unique_chars(strings[k])
  {
    var currentUnique := count_unique_chars(strings[i]);
    if currentUnique > maxUnique {
      maxUnique := currentUnique;
      idx := i;
    }
    i := i + 1;
  }
  s := strings[idx];
}
// </vc-code>
