// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method find_max(strings : seq<string>) returns (s : string)

    requires |strings| > 0

    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
// </vc-spec>
// <vc-code>
{
  s := strings[0];
  var max_unique := |set c | c in s|;
  var i := 1;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant s in strings
    invariant max_unique == |set c | c in s|
    invariant forall j : int :: 0 <= j < i ==> |set c | c in s| >= |set c | c in strings[j]|
  {
    var current_unique := |set c | c in strings[i]|;
    if current_unique > max_unique {
      s := strings[i];
      max_unique := current_unique;
    }
    i := i + 1;
  }
}
// </vc-code>
