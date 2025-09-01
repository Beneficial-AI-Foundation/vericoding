

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
var s := strings[0];
var i := 1;
while i < |strings|
  invariant forall j : int :: 0 <= j < i ==> |{c | c in s}| >= |{c | c in strings[j]}|
  variant |strings| - i
{
  if |{c | c in strings[i]}| > |{c | c in s}| {
    s := strings[i];
  }
  i := i + 1;
}
return s;
// </vc-code>

