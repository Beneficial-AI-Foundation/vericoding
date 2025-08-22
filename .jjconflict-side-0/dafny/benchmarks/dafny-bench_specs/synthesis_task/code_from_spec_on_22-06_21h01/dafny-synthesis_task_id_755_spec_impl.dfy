// ATOM
function MinPair(s: seq<int>) : (r: int)
    requires |s| == 2
    ensures s[0] <= s[1] <==> r == s[0]
    ensures s[0] > s[1] ==> r == s[1] 
{
    if s[0] <= s[1] then s[0] else s[1]
}

// ATOM
function min(s: seq<int>) : (r: int)
    requires |s| >= 2
    ensures forall i :: 0 <= i < |s| ==> r <= s[i]
{
    if |s| == 2 then MinPair(s)
    else MinPair([s[0], min(s[1..])])
}

// IMPL SecondSmallest
method SecondSmallest(s: array<int>) returns (secondSmallest: int)
    requires s.Length >= 2
    // There must be at least 2 different values, a minimum and another one
    requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] != s[i]
    ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] == secondSmallest 
    ensures forall k ::  0 <= k < s.Length && s[k] != min(s[..])  ==>  s[k] >= secondSmallest
{
    var minValue := min(s[..]);
    var secondSmallestValue := s[0];
    
    // Find the first non-minimum value to initialize secondSmallest
    var i := 0;
    while i < s.Length && s[i] == minValue
        invariant 0 <= i <= s.Length
        invariant forall k :: 0 <= k < i ==> s[k] == minValue
    {
        i := i + 1;
    }
    
    secondSmallestValue := s[i];
    
    // Find the actual second smallest among all non-minimum values
    i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant secondSmallestValue != minValue
        invariant exists j :: 0 <= j < s.Length && s[j] == secondSmallestValue && s[j] != minValue
        invariant forall k :: 0 <= k < i && s[k] != minValue ==> s[k] >= secondSmallestValue
    {
        if s[i] != minValue && s[i] < secondSmallestValue {
            secondSmallestValue := s[i];
        }
        i := i + 1;
    }
    
    secondSmallest := secondSmallestValue;
}