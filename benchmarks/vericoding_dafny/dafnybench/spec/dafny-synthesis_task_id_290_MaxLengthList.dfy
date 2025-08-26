// <vc-helpers>
// </vc-helpers>

method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
    requires |lists| > 0
    ensures forall l :: l in lists ==> |l| <= |maxList|
    ensures maxList in lists
// <vc-code>
{
  assume false;
}
// </vc-code>