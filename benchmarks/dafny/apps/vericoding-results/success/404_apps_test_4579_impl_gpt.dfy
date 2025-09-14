function DistinctStrings(strings: seq<string>): set<string>
{
    set i | 0 <= i < |strings| :: strings[i]
}

predicate ValidInput(strings: seq<string>)
{
    |strings| >= 1
}

// <vc-helpers>

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
  var acc: set<string> := {};
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant acc == (set j | 0 <= j < i :: strings[j])
    invariant |acc| <= i
    invariant i > 0 ==> |acc| >= 1
    decreases |strings| - i
  {
    if strings[i] !in acc {
      acc := acc + { strings[i] };
    }
    i := i + 1;
  }
  count := |acc|;
  assert i >= |strings|;
  assert i <= |strings|;
  assert i == |strings|;
  assert acc == DistinctStrings(strings);
}
// </vc-code>

