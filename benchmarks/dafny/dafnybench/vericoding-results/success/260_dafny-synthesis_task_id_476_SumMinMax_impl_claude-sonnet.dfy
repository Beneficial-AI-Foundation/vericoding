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
lemma MinCorrectness(a: seq<int>, minSoFar: int, i: int)
    requires 0 <= i <= |a|
    requires |a| > 0
    requires i > 0 ==> minSoFar == Min(a[..i])
    ensures i == |a| ==> minSoFar == Min(a)
{
    if i == |a| {
        assert a[..i] == a;
    }
}

lemma MaxCorrectness(a: seq<int>, maxSoFar: int, i: int)
    requires 0 <= i <= |a|
    requires |a| > 0
    requires i > 0 ==> maxSoFar == Max(a[..i])
    ensures i == |a| ==> maxSoFar == Max(a)
{
    if i == |a| {
        assert a[..i] == a;
    }
}

lemma MinExtension(a: seq<int>, i: int)
    requires 0 < i < |a|
    ensures Min(a[..i+1]) == if a[i] <= Min(a[..i]) then a[i] else Min(a[..i])
{
    var prefix := a[..i+1];
    var shorterPrefix := a[..i];
    assert prefix == shorterPrefix + [a[i]];
    assert |prefix| == i + 1;
    assert prefix[|prefix|-1] == a[i];
    assert prefix[..|prefix|-1] == shorterPrefix;
}

lemma MaxExtension(a: seq<int>, i: int)
    requires 0 < i < |a|
    ensures Max(a[..i+1]) == if a[i] >= Max(a[..i]) then a[i] else Max(a[..i])
{
    var prefix := a[..i+1];
    var shorterPrefix := a[..i];
    assert prefix == shorterPrefix + [a[i]];
    assert |prefix| == i + 1;
    assert prefix[|prefix|-1] == a[i];
    assert prefix[..|prefix|-1] == shorterPrefix;
}
// </vc-helpers>

// <vc-spec>
method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
// </vc-spec>
// <vc-code>
{
    var minSoFar := a[0];
    var maxSoFar := a[0];
    var i := 1;
    
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant minSoFar == Min(a[..i])
        invariant maxSoFar == Max(a[..i])
    {
        if a[i] <= minSoFar {
            minSoFar := a[i];
        }
        MinExtension(a[..], i);
        
        if a[i] >= maxSoFar {
            maxSoFar := a[i];
        }
        MaxExtension(a[..], i);
        
        i := i + 1;
    }
    
    MinCorrectness(a[..], minSoFar, i);
    MaxCorrectness(a[..], maxSoFar, i);
    sum := minSoFar + maxSoFar;
}
// </vc-code>

