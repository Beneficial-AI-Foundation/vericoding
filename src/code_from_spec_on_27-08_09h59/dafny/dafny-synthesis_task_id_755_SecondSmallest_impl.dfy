function MinPair(s: seq<int>) : (r: int)
    requires |s| == 2
    ensures s[0] <= s[1] <==> r == s[0]
    ensures s[0] > s[1] ==> r == s[1] 
{
    if s[0] <= s[1] then s[0] else s[1]
}


function min(s: seq<int>) : (r: int)
    requires |s| >= 2
    ensures forall i :: 0 <= i < |s| ==> r <= s[i]
{
    if |s| == 2 then MinPair(s)
    else MinPair([s[0], min(s[1..])])
}

// <vc-helpers>
lemma MinInSequence(s: seq<int>)
    requires |s| >= 2
    ensures exists i :: 0 <= i < |s| && s[i] == min(s)
{
    if |s| == 2 {
        if s[0] <= s[1] {
            assert s[0] == min(s);
        } else {
            assert s[1] == min(s);
        }
    } else {
        MinInSequence(s[1..]);
        var minRest := min(s[1..]);
        assert exists i :: 0 <= i < |s[1..]| && s[1..][i] == minRest;
        var k :| 0 <= k < |s[1..]| && s[1..][k] == minRest;
        if s[0] <= minRest {
            assert s[0] == min(s);
        } else {
            assert s[k+1] == min(s);
        }
    }
}

lemma MinIsSmallest(s: seq<int>)
    requires |s| >= 2
    ensures forall i :: 0 <= i < |s| ==> min(s) <= s[i]
{
    // This follows directly from the postcondition of min function
}

lemma NonMinimumExists(s: seq<int>)
    requires |s| >= 2
    requires exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] == min(s) && s[j] != s[i]
    ensures exists k :: 0 <= k < |s| && s[k] != min(s)
{
    var minVal := min(s);
    assert exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] == minVal && s[j] != s[i];
    var i, j :| 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] == minVal && s[j] != s[i];
    MinIsSmallest(s);
    assert minVal <= s[j];
    assert s[j] != minVal;
    assert s[j] != min(s);
}

lemma FindNonMinimumValue(s: array<int>, minimum: int)
    requires s.Length >= 2
    requires minimum == min(s[..])
    requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == minimum && s[j] != s[i]
    ensures exists idx :: 0 <= idx < s.Length && s[idx] != minimum
{
    NonMinimumExists(s[..]);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SecondSmallest(s: array<int>) returns (secondSmallest: int)
    requires s.Length >= 2
    // There must be at least 2 different values, a minimum and another one
    requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] != s[i]
    ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] == secondSmallest 
    ensures forall k ::  0 <= k < s.Length && s[k] != min(s[..])  ==>  s[k] >= secondSmallest
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var minimum := min(s[..]);
    var secondMin := s[0];
    var foundSecond := false;
    var secondMinIndex := 0;
    
    // Find the first element that's not the minimum
    FindNonMinimumValue(s, minimum);
    var i := 0;
    while i < s.Length && !foundSecond
        invariant 0 <= i <= s.Length
        invariant !foundSecond ==> forall k :: 0 <= k < i ==> s[k] == minimum
        invariant foundSecond ==> secondMin != minimum
        invariant foundSecond ==> secondMinIndex < i && s[secondMinIndex] == secondMin
    {
        if s[i] != minimum {
            secondMin := s[i];
            secondMinIndex := i;
            foundSecond := true;
        }
        i := i + 1;
    }
    
    // At this point, secondMin is some non-minimum element
    assert foundSecond;
    assert secondMin != minimum;
    assert s[secondMinIndex] == secondMin;
    MinIsSmallest(s[..]);
    
    // Find the actual second smallest among non-minimum elements
    i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant forall k :: 0 <= k < i && s[k] != minimum ==> s[k] >= secondMin
        invariant exists j :: 0 <= j < s.Length && s[j] != minimum && s[j] == secondMin
        invariant secondMin != minimum
    {
        if s[i] != minimum && s[i] < secondMin {
            secondMin := s[i];
        }
        i := i + 1;
    }
    
    secondSmallest := secondMin;
}
// </vc-code>
