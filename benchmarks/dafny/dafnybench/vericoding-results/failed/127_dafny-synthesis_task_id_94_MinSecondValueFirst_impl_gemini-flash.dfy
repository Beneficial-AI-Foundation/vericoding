

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
// </vc-spec>
// <vc-code>
{
    var minSecond: int := s[0][1];
    var firstOfMinSecondResult: int := s[0][0];

    var i: int := 1;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant exists k :: 0 <= k < i && firstOfMinSecondResult == s[k][0] && minSecond == s[k][1] && (forall j :: 0 <= j < i ==> s[k][1] <= s[j][1])
        invariant forall j :: 0 <= j < i ==> minSecond <= s[j][1]
    {
        if s[i][1] < minSecond {
            minSecond := s[i][1];
            firstOfMinSecondResult := s[i][0];
        } else if s[i][1] == minSecond {
        }
        i := i + 1;
    }
    return firstOfMinSecondResult;
}
// </vc-code>

