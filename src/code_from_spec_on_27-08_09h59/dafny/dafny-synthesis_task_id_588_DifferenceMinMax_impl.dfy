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
    ensures forall i :: 0 <= i < |a| ==> Min(a) <= a[i] <= Max(a)
{
    if |a| == 1 {
        assert a == [a[0]];
        assert Min(a) == a[0] == Max(a);
    } else {
        var prefix := a[..|a|-1];
        assert |prefix| > 0;
        MinMaxProperties(prefix);
        
        var minPrefix := Min(prefix);
        var maxPrefix := Max(prefix);
        
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
    }
}

lemma MinCorrectness(a: seq<int>, currentMin: int)
    requires |a| > 0
    requires forall j :: 0 <= j < |a| ==> currentMin <= a[j]
    requires exists j :: 0 <= j < |a| && currentMin == a[j]
    ensures currentMin == Min(a)
{
    MinMaxProperties(a);
    
    // currentMin is a lower bound for all elements
    assert forall j :: 0 <= j < |a| ==> currentMin <= a[j];
    
    // Min(a) is also a lower bound for all elements
    assert forall j :: 0 <= j < |a| ==> Min(a) <= a[j];
    
    // currentMin is an element of the sequence
    assert exists k :: 0 <= k < |a| && currentMin == a[k];
    
    // Since Min(a) is a lower bound and currentMin is an element, Min(a) <= currentMin
    assert Min(a) <= currentMin;
    
    // Since currentMin is a lower bound and Min(a) is an element, currentMin <= Min(a)
    // We need to show that Min(a) is actually in the sequence
    assert exists m :: 0 <= m < |a| && Min(a) == a[m] by {
        MinIsElement(a);
    }
    assert currentMin <= Min(a);
}

lemma MaxCorrectness(a: seq<int>, currentMax: int)
    requires |a| > 0
    requires forall j :: 0 <= j < |a| ==> a[j] <= currentMax
    requires exists j :: 0 <= j < |a| && currentMax == a[j]
    ensures currentMax == Max(a)
{
    MinMaxProperties(a);
    
    // currentMax is an upper bound for all elements
    assert forall j :: 0 <= j < |a| ==> a[j] <= currentMax;
    
    // Max(a) is also an upper bound for all elements
    assert forall j :: 0 <= j < |a| ==> a[j] <= Max(a);
    
    // currentMax is an element of the sequence
    assert exists k :: 0 <= k < |a| && currentMax == a[k];
    
    // Since currentMax is an upper bound and Max(a) is an element, currentMax >= Max(a)
    assert exists m :: 0 <= m < |a| && Max(a) == a[m] by {
        MaxIsElement(a);
    }
    assert currentMax >= Max(a);
    
    // Since Max(a) is an upper bound and currentMax is an element, Max(a) >= currentMax
    assert Max(a) >= currentMax;
}

lemma MinIsElement(a: seq<int>)
    requires |a| > 0
    ensures exists i :: 0 <= i < |a| && Min(a) == a[i]
{
    if |a| == 1 {
        assert Min(a) == a[0];
    } else {
        var prefix := a[..|a|-1];
        MinIsElement(prefix);
        var minPrefix := Min(prefix);
        if a[|a|-1] <= minPrefix {
            assert Min(a) == a[|a|-1];
        } else {
            assert Min(a) == minPrefix;
            assert exists j :: 0 <= j < |prefix| && minPrefix == prefix[j];
        }
    }
}

lemma MaxIsElement(a: seq<int>)
    requires |a| > 0
    ensures exists i :: 0 <= i < |a| && Max(a) == a[i]
{
    if |a| == 1 {
        assert Max(a) == a[0];
    } else {
        var prefix := a[..|a|-1];
        MaxIsElement(prefix);
        var maxPrefix := Max(prefix);
        if a[|a|-1] >= maxPrefix {
            assert Max(a) == a[|a|-1];
        } else {
            assert Max(a) == maxPrefix;
            assert exists j :: 0 <= j < |prefix| && maxPrefix == prefix[j];
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
{
    var currentMin := a[0];
    var currentMax := a[0];
    var i := 1;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> currentMin <= a[j] <= currentMax
        invariant exists j :: 0 <= j < i && currentMin == a[j]
        invariant exists j :: 0 <= j < i && currentMax == a[j]
    {
        if a[i] < currentMin {
            currentMin := a[i];
        }
        if a[i] > currentMax {
            currentMax := a[i];
        }
        i := i + 1;
    }
    
    assert i == a.Length;
    assert forall j :: 0 <= j < a.Length ==> currentMin <= a[j] <= currentMax;
    assert exists j :: 0 <= j < a.Length && currentMin == a[j];
    assert exists j :: 0 <= j < a.Length && currentMax == a[j];
    
    MinCorrectness(a[..], currentMin);
    assert currentMin == Min(a[..]);
    MaxCorrectness(a[..], currentMax);
    assert currentMax == Max(a[..]);
    
    diff := currentMax - currentMin;
}
// </vc-code>
