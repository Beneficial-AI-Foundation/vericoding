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
  var distinct: set<string> := {};
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant distinct == set j | 0 <= j < i :: strings[j]
    invariant |distinct| >= (if i>0 then 1 else 0)
    invariant |distinct| <= i
  {
    distinct := distinct + {strings[i]};
    i := i + 1;
  }
  return |distinct|;
}
// </vc-code>

