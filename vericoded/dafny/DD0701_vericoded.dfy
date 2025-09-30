

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
    maxList := lists[0];
    var i := 1;
    
    while i < |lists|
        invariant 1 <= i <= |lists|
        invariant maxList in lists[0..i]
        invariant forall j :: 0 <= j < i ==> |lists[j]| <= |maxList|
    {
        if |lists[i]| > |maxList| {
            maxList := lists[i];
        }
        i := i + 1;
    }
}
// </vc-code>

