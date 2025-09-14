function Power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * Power(base, exponent-1)
}

// <vc-helpers>
lemma PowerLemma(a: int, b: int, n: int)
    requires n >= 0
    ensures Power(a * b, n) == Power(a, n) * Power(b, n)
{
    if n == 0 {
    } else {
        PowerLemma(a, b, n-1);
    }
}

lemma PowerOfZero(n: int)
    requires n >= 0
    ensures Power(0, n) == (if n == 0 then 1 else 0)
{
}

lemma SequenceLengthLemma(s: seq<int>, x: int)
    ensures |s + [x]| == |s| + 1
{
}

lemma SequenceIndexLemma(s: seq<int>, x: int, j: int)
    requires 0 <= j < |s|
    ensures (s + [x])[j] == s[j]
{
}

lemma SequenceLastIndexLemma(s: seq<int>, x: int)
    ensures (s + [x])[|s|] == x
{
}
// </vc-helpers>
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
    var index := 0;
    
    while index < |l|
        invariant 0 <= index <= |l|
        invariant |result| == index
        invariant forall j :: 0 <= j < index ==> result[j] == Power(l[j], n)
    {
        var power_val := Power(l[index], n);
        result := result + [power_val];
        index := index + 1;
    }
}
// </vc-code>

