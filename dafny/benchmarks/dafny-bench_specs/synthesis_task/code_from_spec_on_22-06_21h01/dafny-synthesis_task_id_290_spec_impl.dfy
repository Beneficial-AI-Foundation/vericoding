//IMPL
method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
    requires |lists| > 0
    ensures forall l :: l in lists ==> |l| <= |maxList|
    ensures maxList in lists
{
    maxList := lists[0];
    var i := 1;
    
    while i < |lists|
        invariant 0 <= i <= |lists|
        invariant maxList in lists
        invariant forall j :: 0 <= j < i ==> |lists[j]| <= |maxList|
    {
        if |lists[i]| > |maxList| {
            maxList := lists[i];
        }
        i := i + 1;
    }
}