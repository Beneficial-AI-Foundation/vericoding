// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function unique_chars_count(s: string): nat { |set c | c in s| }
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
  var i: nat := 1;
  while i < |strings|
    invariant 1 <= i <= |strings|
    invariant s in strings[..i]
    invariant forall j: int :: 0 <= j < i ==> unique_chars_count(s) >= unique_chars_count(strings[j])
  {
    if unique_chars_count(strings[i]) > unique_chars_count(s) {
      s := strings[i];
    }
    i := i + 1;
  }
}
// </vc-code>
