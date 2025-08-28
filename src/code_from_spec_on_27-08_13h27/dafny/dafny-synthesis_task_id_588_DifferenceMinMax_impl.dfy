// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
function Min(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var minPrefix := Min(a[..|a|-1]);
        if a[|a|-1] <= minPrefix then a[|a|-1] else Min(a[..|a|-1])
}

function Max(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var maxPrefix := Max(a[..|a|-1]);
        if a[|a|-1] >= maxPrefix then a[|a|-1] else Max(a[..|a|-1])
}

// <vc-helpers>
lemma MinMaxProperties(a: seq<int>)
    requires |a| > 0
    ensures forall i :: 0 <= i < |a| ==> Min(a) <= a[i]
    ensures forall i :: 0 <= i < |a| ==> Max(a) >= a[i]
    ensures Min(a) in a
    ensures Max(a) in a
{
    if |a| == 1 {
        assert Min(a) == a[0];
        assert Max(a) == a[0];
    } else {
        MinMaxProperties(a[..|a|-1]);
        var minPrefix := Min(a[..|a|-1]);
        var maxPrefix := Max(a[..|a|-1]);
        if a[|a|-1] <= minPrefix {
            assert Min(a) == a[|a|-1];
        } else {
            assert Min(a) == minPrefix;
        }
        if a[|a|-1] >= maxPrefix {
            assert Max(a) == a[|a|-1];
        } else {
            assert Max(a) == maxPrefix;
        }
        for i := 0 to |a|-1
            invariant forall k :: 0 <= k < i ==> Min(a) <= a[k]
            invariant forall k :: 0 <= k < i ==> Max(a) >= a[k]
        {
            assert Min(a) <= minPrefix <= a[i];
            assert Max(a) >= maxPrefix >= a[i];
        }
        assert Min(a) <= a[|a|-1];
        assert Max(a) >= a[|a|-1];
    }
}

lemma MinMaxSlice(a: seq<int>, i: int)
    requires 0 < i <= |a|
    ensures Min(a[..i]) == if i == 1 then a[0] else if a[i-1] < Min(a[..i-1]) then a[i-1] else Min(a[..i-1])
    ensures Max(a[..i]) == if i == 1 then a[0] else if a[i-1] > Max(a[..i-1]) then a[i-1] else Max(a[..i-1])
{
    if i == 1 {
        assert a[..1] == [a[0]];
    } else {
        MinMaxSlice(a, i-1);
        assert a[..i] == a[..i-1] + [a[i-1]];
        var minPrefix := Min(a[..i-1]);
        var maxPrefix := Max(a[..i-1]);
        if a[i-1] < minPrefix {
            assert Min(a[..i]) == a[i-1];
        } else {
            assert Min(a[..i]) == minPrefix;
        }
        if a[i-1] > maxPrefix {
            assert Max(a[..i]) == a[i-1];
        } else {
            assert Max(a[..i]) == maxPrefix;
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == Max(a[..]) - Min(a[..])
// </vc-spec>
// </vc-spec>

// <vc-code>
method ComputeDifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == Max(a[..]) - Min(a[..])
{
    var minVal := a[0];
    var maxVal := a[0];
    var i := 1;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> minVal <= a[k]
        invariant forall k :: 0 <= k < i ==> maxVal >= a[k]
        invariant minVal == Min(a[..i])
        invariant maxVal == Max(a[..i])
    {
        MinMaxSlice(a[..], i);
        if a[i] < minVal {
            minVal := a[i];
        }
        if a[i] > maxVal {
            maxVal := a[i];
        }
        i := i + 1;
        assert a[..i] == a[..i-1] + [a[i-1]];
    }
    assert a[..i] == a[..];
    diff := maxVal - minVal;
}
// </vc-code>
