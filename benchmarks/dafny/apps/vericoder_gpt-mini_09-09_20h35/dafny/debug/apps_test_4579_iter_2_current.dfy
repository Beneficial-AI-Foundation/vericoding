function DistinctStrings(strings: seq<string>): set<string>
{
    set i | 0 <= i < |strings| :: strings[i]
}

predicate ValidInput(strings: seq<string>)
{
    |strings| >= 1
}

// <vc-helpers>
// No additional helpers required.
// </vc-helpers>

// <vc-spec>
method solve(strings: seq<string>) returns (count: int)
    requires ValidInput(strings)
    ensures count >= 1
    ensures count <= |strings|
    ensures count == |DistinctStrings(strings)|
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var seen: set<string> := {};
  var c := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant seen == DistinctStrings(strings[..i])
    invariant c == |seen|
  {
    seen := DistinctStrings(strings[..i+1]);
    c := |seen|;
    i := i + 1;
  }
  count := c;
}
// </vc-code>

