// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function countUniqueChars(s: string): nat { |set c | c in s| }
// </vc-helpers>

// <vc-spec>
method find_max(strings : seq<string>) returns (s : string)

    requires |strings| > 0

    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
// </vc-spec>
// <vc-code>
{
  var max_s := strings[0];
  var i := 1;
  while i < |strings|
    invariant 1 <= i <= |strings|
    invariant max_s in strings
    invariant forall j :: 0 <= j < i ==> countUniqueChars(max_s) >= countUniqueChars(strings[j])
  {
    if countUniqueChars(strings[i]) > countUniqueChars(max_s) {
      max_s := strings[i];
    }
    i := i + 1;
  }
  s := max_s;
}
// </vc-code>
