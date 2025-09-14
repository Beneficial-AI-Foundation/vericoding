

// <vc-helpers>
lemma MaxLengthLemma(lists: seq<seq<int>>, maxList: seq<int>)
  requires |lists| > 0
  requires maxList in lists
  requires forall l :: l in lists[0..|lists|] ==> |l| <= |maxList|
  ensures forall l :: l in lists ==> |l| <= |maxList|
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
    requires |lists| > 0
    ensures forall l :: l in lists ==> |l| <= |maxList|
    ensures maxList in lists
// </vc-spec>
// <vc-code>
{
  maxList := lists[0];
  var i := 1;
  while i < |lists|
    invariant 0 <= i <= |lists|
    invariant maxList in lists
    invariant forall l :: l in lists[0..i] ==> |l| <= |maxList|
  {
    if |lists[i]| > |maxList| {
      maxList := lists[i];
    }
    i := i + 1;
  }
  MaxLengthLemma(lists, maxList);
}
// </vc-code>

