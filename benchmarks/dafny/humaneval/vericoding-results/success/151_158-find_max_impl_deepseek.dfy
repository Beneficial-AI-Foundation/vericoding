// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function maxCharCount(s: string): int ensures maxCharCount(s) == |set c | c in s| { if |s| == 0 then 0 else |set c | c in s| }
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
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant s in strings
    invariant forall j: int :: 0 <= j < i ==> |set c | c in s| >= |set c | c in strings[j]|
  {
    var currentCount := maxCharCount(strings[i]);
    var sCount := maxCharCount(s);
    if currentCount > sCount {
      s := strings[i];
    }
    i := i + 1;
  }
}
// </vc-code>
