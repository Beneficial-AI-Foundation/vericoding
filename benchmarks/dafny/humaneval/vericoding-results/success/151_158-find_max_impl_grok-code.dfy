// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added helper function to compute unique character count */
function UniqueCount(s: string): int
ensures UniqueCount(s) == |set c | c in s|
{
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
/* code modified by LLM (iteration 2): Added loop invariants to prove postconditions */
{
  var max_str := strings[0];
  var max_uniques := UniqueCount(max_str);
  var i := 1;
  while i < |strings|
    invariant 1 <= i <= |strings|
    invariant max_str in strings[..i]
    invariant max_uniques == UniqueCount(max_str)
    invariant forall j :: 0 <= j < i ==> max_uniques >= UniqueCount(strings[j])
  {
    var current_uniques := UniqueCount(strings[i]);
    if current_uniques > max_uniques {
      max_str := strings[i];
      max_uniques := current_uniques;
    }
    i := i + 1;
  }
  s := max_str;
}
// </vc-code>
