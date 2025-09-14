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
lemma MinMaxPrefix(a: seq<int>, i: int)
    requires 0 < i <= |a|
    ensures i == |a| ==> Min(a[..i]) == Min(a) && Max(a[..i]) == Max(a)
    ensures i < |a| ==> Min(a[..i+1]) == if a[i] < Min(a[..i]) then a[i] else Min(a[..i])
    ensures i < |a| ==> Max(a[..i+1]) == if a[i] > Max(a[..i]) then a[i] else Max(a[..i])
{
    if i == |a| {
        assert a[..i] == a;
    } else if i == 1 {
        assert a[..1] == [a[0]];
        assert Min(a[..1]) == a[0];
        assert Max(a[..1]) == a[0];
        assert a[..i+1] == a[..2];
        if |a| >= 2 {
            assert a[..2] == [a[0], a[1]];
        }
    } else {
        assert a[..i+1][..i] == a[..i];
    }
}
// </vc-helpers>

// <vc-spec>
method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
// </vc-spec>
// <vc-code>
{
    var minVal := a[0];
    var maxVal := a[0];
    var i := 1;
    
    assert a[..1] == [a[0]];
    assert Min(a[..1]) == a[0];
    assert Max(a[..1]) == a[0];
    
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant minVal == Min(a[..i])
        invariant maxVal == Max(a[..i])
    {
        MinMaxPrefix(a[..], i);
        
        if a[i] < minVal {
            minVal := a[i];
        }
        if a[i] > maxVal {
            maxVal := a[i];
        }
        
        i := i + 1;
    }
    
    assert i == a.Length;
    assert a[..a.Length] == a[..];
    MinMaxPrefix(a[..], a.Length);
    
    sum := maxVal + minVal;
}
// </vc-code>

