

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
  var i := 1;
  var best := 0;
  while i < |lists|
    invariant 1 <= i <= |lists|
    invariant 0 <= best < i
    invariant forall k :: 0 <= k < i ==> |lists[k]| <= |lists[best]|
    decreases |lists| - i
  {
    if |lists[i]| > |lists[best]| {
      best := i;
    }
    i := i + 1;
  }
  maxList := lists[best];
}
// </vc-code>

