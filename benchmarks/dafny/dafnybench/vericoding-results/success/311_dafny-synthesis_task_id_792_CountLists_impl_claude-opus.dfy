

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountLists(lists: seq<seq<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |lists|
// </vc-spec>
// <vc-code>
{
    count := |lists|;
}
// </vc-code>

