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
lemma MinPrefix(a: seq<int>, i: int)
    requires 0 < i <= |a|
    ensures Min(a[..i]) == if i == 1 then a[0] 
                          else if a[i-1] <= Min(a[..i-1]) then a[i-1] 
                          else Min(a[..i-1])
{
    assert a[..i][..i-1] == a[..i-1];
}

lemma MaxPrefix(a: seq<int>, i: int)
    requires 0 < i <= |a|
    ensures Max(a[..i]) == if i == 1 then a[0]
                          else if a[i-1] >= Max(a[..i-1]) then a[i-1]
                          else Max(a[..i-1])
{
    assert a[..i][..i-1] == a[..i-1];
}
// </vc-helpers>

// <vc-spec>
method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == Max(a[..]) - Min(a[..])
// </vc-spec>
// <vc-code>
{
    var minVal := a[0];
    var maxVal := a[0];
    var i := 1;
    
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant minVal == Min(a[..i])
        invariant maxVal == Max(a[..i])
    {
        MinPrefix(a[..], i+1);
        MaxPrefix(a[..], i+1);
        
        if a[i] < minVal {
            minVal := a[i];
        }
        if a[i] > maxVal {
            maxVal := a[i];
        }
        i := i + 1;
    }
    
    assert a[..a.Length] == a[..];
    diff := maxVal - minVal;
}
// </vc-code>

