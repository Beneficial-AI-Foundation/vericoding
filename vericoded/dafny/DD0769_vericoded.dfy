function Power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * Power(base, exponent-1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
    requires n >= 0
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
// </vc-spec>
// <vc-code>
{
    result := [];
    for i := 0 to |l|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == Power(l[j], n)
    {
        result := result + [Power(l[i], n)];
    }
}
// </vc-code>

