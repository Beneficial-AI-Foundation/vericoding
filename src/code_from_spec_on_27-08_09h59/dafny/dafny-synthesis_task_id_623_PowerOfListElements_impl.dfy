function Power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * Power(base, exponent-1)
}

// <vc-helpers>
lemma PowerProperties(base: int, exp: int)
    requires exp >= 0
    ensures Power(base, exp) == Power(base, exp)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
    requires n >= 0
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    result := [];
    var i := 0;
    while i < |l|
        invariant 0 <= i <= |l|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == Power(l[j], n)
    {
        var powerValue := Power(l[i], n);
        result := result + [powerValue];
        i := i + 1;
    }
}
// </vc-code>
