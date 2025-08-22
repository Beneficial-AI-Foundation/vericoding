//IMPL 
method PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
    requires n >= 0
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
{
    result := [];
    var i := 0;
    while i < |l|
        invariant 0 <= i <= |l|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == Power(l[j], n)
    {
        result := result + [Power(l[i], n)];
        i := i + 1;
    }
}


//ATOM 

function Power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * Power(base, exponent-1)
}