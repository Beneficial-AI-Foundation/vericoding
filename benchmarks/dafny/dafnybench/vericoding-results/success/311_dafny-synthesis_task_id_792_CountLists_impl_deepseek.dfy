

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountLists(lists: seq<seq<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |lists|
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  while i < |lists|
    invariant count == i
    invariant i <= |lists|
    invariant count >= 0
  {
    count := count + 1;
    i := i + 1;
  }
}
// </vc-code>

