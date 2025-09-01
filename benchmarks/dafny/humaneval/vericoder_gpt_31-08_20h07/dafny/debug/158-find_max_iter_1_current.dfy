

// <vc-helpers>
function method distinctCount(s: string): nat
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
{
  var max := 0;
  var i := 1;
  while i < |strings|
    invariant 0 <= max < |strings|
    invariant 1 <= i <= |strings|
    invariant max < i
    invariant forall j:int :: 0 <= j < i ==> distinctCount(strings[max]) >= distinctCount(strings[j])
    decreases |strings| - i
  {
    var oldI := i;
    if distinctCount(strings[i]) > distinctCount(strings[max]) {
      assert forall j:int :: 0 <= j < i ==> distinctCount(strings[i]) >= distinctCount(strings[j]);
      max := i;
    } else {
      assert distinctCount(strings[i]) <= distinctCount(strings[max]);
    }
    assert distinctCount(strings[max]) >= distinctCount(strings[oldI]);
    i := i + 1;
  }
  s := strings[max];
}
// </vc-code>

