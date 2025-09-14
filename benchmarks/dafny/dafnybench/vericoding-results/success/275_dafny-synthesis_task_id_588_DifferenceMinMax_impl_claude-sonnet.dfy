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
lemma MinCorrectness(a: seq<int>, minVal: int)
    requires |a| > 0
    requires minVal == Min(a)
    ensures forall i :: 0 <= i < |a| ==> minVal <= a[i]
    ensures exists i :: 0 <= i < |a| && minVal == a[i]
{
    if |a| == 1 {
        assert minVal == a[0];
    } else {
        var minPrefix := Min(a[..|a|-1]);
        MinCorrectness(a[..|a|-1], minPrefix);
        if a[|a|-1] <= minPrefix {
            assert minVal == a[|a|-1];
        } else {
            assert minVal == minPrefix;
            MinCorrectness(a[..|a|-1], minVal);
        }
    }
}

lemma MaxCorrectness(a: seq<int>, maxVal: int)
    requires |a| > 0
    requires maxVal == Max(a)
    ensures forall i :: 0 <= i < |a| ==> maxVal >= a[i]
    ensures exists i :: 0 <= i < |a| && maxVal == a[i]
{
    if |a| == 1 {
        assert maxVal == a[0];
    } else {
        var maxPrefix := Max(a[..|a|-1]);
        MaxCorrectness(a[..|a|-1], maxPrefix);
        if a[|a|-1] >= maxPrefix {
            assert maxVal == a[|a|-1];
        } else {
            assert maxVal == maxPrefix;
            MaxCorrectness(a[..|a|-1], maxVal);
        }
    }
}

lemma MinExtension(a: seq<int>, x: int)
    requires |a| > 0
    ensures Min(a + [x]) == if x <= Min(a) then x else Min(a)
{
    var extended := a + [x];
    assert extended[..|extended|-1] == a;
    assert extended[|extended|-1] == x;
}

lemma MaxExtension(a: seq<int>, x: int)
    requires |a| > 0
    ensures Max(a + [x]) == if x >= Max(a) then x else Max(a)
{
    var extended := a + [x];
    assert extended[..|extended|-1] == a;
    assert extended[|extended|-1] == x;
}

lemma ArraySliceExtension(a: array<int>, i: int)
    requires 0 <= i < a.Length
    ensures a[..i+1] == a[..i] + [a[i]]
{
    assert a[..i+1][..i] == a[..i];
    assert a[..i+1][i] == a[i];
}
// </vc-helpers>

// <vc-spec>
method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == Max(a[..]) - Min(a[..])
// </vc-spec>
// <vc-code>
{
    var min := a[0];
    var max := a[0];
    var i := 1;
    
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant min == Min(a[..i])
        invariant max == Max(a[..i])
    {
        ArraySliceExtension(a, i);
        assert a[..i+1] == a[..i] + [a[i]];
        
        MinExtension(a[..i], a[i]);
        MaxExtension(a[..i], a[i]);
        
        if a[i] < min {
            min := a[i];
            assert min == Min(a[..i+1]);
        } else {
            assert min == Min(a[..i+1]);
        }
        
        if a[i] > max {
            max := a[i];
            assert max == Max(a[..i+1]);
        } else {
            assert max == Max(a[..i+1]);
        }
        
        i := i + 1;
    }
    
    assert i == a.Length;
    assert a[..i] == a[..];
    assert min == Min(a[..]);
    assert max == Max(a[..]);
    
    diff := max - min;
}
// </vc-code>

