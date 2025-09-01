

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
var max_s : string := strings[0];
var max_count : nat := |set c: char | c in strings[0]|;

assert max_count == |set c: char | c in strings[0]|;

for i := 1 to |strings|
  invariant 0 <= i <= |strings|
  invariant max_s in strings[..i]
  invariant max_count == |set c: char | c in max_s|
  invariant forall j :: 0 <= j < i ==> max_count >= |set c: char | c in strings[j]|
{
  var current_count := |set c: char | c in strings[i]|;
  if current_count > max_count {
    max_s := strings[i];
    max_count := current_count;
  }
}

return max_s;
// </vc-code>

