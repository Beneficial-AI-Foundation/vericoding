

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
    requires |lists| > 0
    ensures forall l :: l in lists ==> |l| <= |maxList|
    ensures maxList in lists
// </vc-spec>
// <vc-code>
{
  var n := |lists|;
  var best := lists[0];
  var i := 1;
  while i < n
    invariant 0 <= i <= n
    invariant best in lists[0..i]
    invariant forall j :: 0 <= j < i ==> |lists[j]| <= |best|
    decreases n - i
  {
    var cur := lists[i];
    if |cur| >= |best| {
      best := cur;
    }
    i := i + 1;
  }
  maxList := best;
}
// </vc-code>

