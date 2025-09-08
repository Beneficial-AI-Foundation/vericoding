Given a sequence of N integers, for each position i, find the maximum value 
among all N-1 elements excluding the element at position i.

function max_of_seq(s: seq<int>): int
    requires |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> s[i] <= max_of_seq(s)
    ensures exists i :: 0 <= i < |s| && s[i] == max_of_seq(s)
{
    if |s| == 1 then s[0]
    else if s[0] >= max_of_seq(s[1..]) then s[0]
    else max_of_seq(s[1..])
}

function max_excluding(s: seq<int>, exclude_idx: int): int
    requires 0 <= exclude_idx < |s|
    requires |s| >= 2
{
    var others := s[..exclude_idx] + s[exclude_idx+1..];
    max_of_seq(others)
}

method solve(input: seq<int>) returns (result: seq<int>)
    requires |input| >= 2
    ensures |result| == |input|
    ensures forall i :: 0 <= i < |input| ==> result[i] == max_excluding(input, i)
{
    result := [];
    var i := 0;
    while i < |input|
        invariant 0 <= i <= |input|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == max_excluding(input, j)
    {
        result := result + [max_excluding(input, i)];
        i := i + 1;
    }
}
