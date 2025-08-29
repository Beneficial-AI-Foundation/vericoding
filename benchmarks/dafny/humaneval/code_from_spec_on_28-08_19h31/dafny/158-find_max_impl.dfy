// <vc-helpers>
function count_unique_chars(s: string): nat
{
  |set c | c in s|
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
method findMax(strings: seq<string>) returns (s: string)
  requires |strings| > 0
  ensures s in strings
  ensures forall i: int :: 0 <= i < |strings| ==> count_unique_chars(s) >= count_unique_chars(strings[i])
{
  s := strings[0];
  var max_unique := count_unique_chars(s);
  var i := 1;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant s in strings
    invariant max_unique == count_unique_chars(s)
    invariant forall j: int :: 0 <= j < i ==> max_unique >= count_unique_chars(strings[j])
  {
    var current_unique := count_unique_chars(strings[i]);
    if current_unique > max_unique {
      s := strings[i];
      max_unique := current_unique;
    }
    i := i + 1;
  }
}
// </vc-code>
