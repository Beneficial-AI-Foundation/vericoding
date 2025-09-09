Given an integer sequence, determine if it can be divided into an odd number of 
non-empty contiguous subsegments, where each subsegment has odd length and 
begins and ends with odd numbers.

predicate ValidInput(a: seq<int>)
{
    |a| >= 1
}

predicate CanBeDivided(a: seq<int>)
    requires ValidInput(a)
{
    |a| % 2 == 1 && a[0] % 2 == 1 && a[|a|-1] % 2 == 1
}

method solve(a: seq<int>) returns (result: string)
    requires ValidInput(a)
    ensures CanBeDivided(a) ==> result == "Yes"
    ensures !CanBeDivided(a) ==> result == "No"
{
    if CanBeDivided(a) {
        result := "Yes";
    } else {
        result := "No";
    }
}
