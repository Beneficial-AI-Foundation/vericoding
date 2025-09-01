

// <vc-helpers>
function CardinalityHelper<T>(s: set<T>): nat
{
  s.Cardinality
}
// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)
  // post-conditions-start
  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var len := |s|;
  var halfLen := len / 2;
  for i := 0 to halfLen - 1
    invariant 0 <= i <= halfLen
    invariant count == (set j | 0 <= j < i && s[j] != s[len - 1 - j] && 0 <= j < |s| && 0 <= len - 1 - j < |s| |).Cardinality
  {
    if s[i] != s[len - 1 - i] {
      count := count + 1;
    }
  }
  return count;
}
// </vc-code>

