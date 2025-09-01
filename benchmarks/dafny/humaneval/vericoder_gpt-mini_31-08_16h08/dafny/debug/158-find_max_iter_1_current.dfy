

// <vc-helpers>

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
  var best := strings[0];
  var i := 1;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant best in strings[..i]
    invariant forall j :: 0 <= j < i ==> |set c | c in best| >= |set c | c in strings[j]|
    decreases |strings| - i
  {
    if |set c | c in strings[i]| > |set c | c in best| {
      best := strings[i];
    }
    i := i + 1;
  }
  s := best;
}
// </vc-code>

