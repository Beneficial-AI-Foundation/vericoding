Given a string of lowercase letters, delete the minimum number of characters to make it "good".
A string is "good" if its length is even and each character at odd positions (1st, 3rd, 5th, ...)
differs from the character at the next even position (2nd, 4th, 6th, ...).

predicate ValidInput(n: int, s: string)
{
    n == |s| && n >= 0
}

predicate IsGoodString(s: string)
{
    |s| % 2 == 0 && forall i :: 0 <= i < |s|/2 ==> s[2*i] != s[2*i+1]
}

method solve(n: int, s: string) returns (deletedCount: int, result: string)
    requires ValidInput(n, s)
    ensures deletedCount >= 0
    ensures deletedCount == |s| - |result|
    ensures IsGoodString(result)
    ensures deletedCount + |result| == |s|
{
    var t := "";
    var lst := '1';

    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |t| % 2 == 0
        invariant |t| + (if lst != '1' then 1 else 0) <= i
        invariant forall j :: 0 <= j < |t|/2 ==> t[2*j] != t[2*j+1]
    {
        var ch := s[i];
        if lst == '1' {
            lst := ch;
        } else {
            if lst != ch {
                t := t + [lst] + [ch];
                lst := '1';
            }
        }
        i := i + 1;
    }

    deletedCount := |s| - |t|;
    result := t;
}
