//IMPL 
method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
{
    var minIndex := 0;
    var i := 1;
    
    while i < s.Length
        invariant 0 <= minIndex < s.Length
        invariant 1 <= i <= s.Length
        invariant forall k :: 0 <= k < i ==> s[minIndex][1] <= s[k][1]
    {
        if s[i][1] < s[minIndex][1] {
            minIndex := i;
        }
        i := i + 1;
    }
    
    firstOfMinSecond := s[minIndex][0];
}