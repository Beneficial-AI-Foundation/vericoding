

// <vc-helpers>
function distinct_chars(s: string) : nat
{
  |{c | c in s}|
}
// </vc-helpers>

// <vc-spec>
method find_max(strings : seq<string>) returns (s : string)
   // pre-conditions-start
    requires |strings| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var s := strings[0];
  var i := 1;
  while i < |strings|
    invariant forall j : int :: 0 <= j < i ==> distinct_chars(s) >= distinct_chars(strings[j])
    variant |strings| - i
  {
    if distinct_chars(strings[i]) > distinct_chars(s) {
      s := strings[i];
    }
    i := i + 1;
  }
  return s;
}
// </vc-code>

