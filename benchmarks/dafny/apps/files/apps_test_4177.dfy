Given a string S consisting of lowercase English letters, replace every character with 'x' and output the result.

predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(s: string, result: string)
{
    |result| == |s| && forall i :: 0 <= i < |result| ==> result[i] == 'x'
}

method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
{
    result := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == 'x'
    {
        result := result + "x";
        i := i + 1;
    }
}
