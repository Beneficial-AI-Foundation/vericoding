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
lemma MinInArray(s: array<int>)
    requires s.Length >= 2
    ensures exists i :: 0 <= i < s.Length && s[i] == min(s[..])
{
    MinExistsInSeq(s[..]);
}

lemma MinExistsInSeq(s: seq<int>)
    requires |s| >= 2
    ensures exists i :: 0 <= i < |s| && s[i] == min(s)
    decreases |s|
{
    if |s| == 2 {
        var minVal := MinPair(s);
        if s[0] <= s[1] {
            assert minVal == s[0];
            assert exists i :: 0 <= i < |s| && s[i] == minVal;
        } else {
            assert minVal == s[1];
            assert exists i :: 0 <= i < |s| && s[i] == minVal;
        }
    } else {
        var tailMin := min(s[1..]);
        MinExistsInSeq(s[1..]);
        assert exists j :: 0 <= j < |s[1..]| && s[1..][j] == tailMin;
        var minVal := min(s);
        var pairMin := MinPair([s[0], tailMin]);
        assert minVal == pairMin;
        
        if s[0] <= tailMin {
            assert minVal == s[0];
            assert exists i :: 0 <= i < |s| && s[i] == minVal;
        } else {
            assert minVal == tailMin;
            var j :| 0 <= j < |s[1..]| && s[1..][j] == tailMin;
            assert s[j+1] == tailMin;
            assert exists i :: 0 <= i < |s| && s[i] == minVal;
        }
    }
}

lemma MinIsSmallest(s: seq<int>, minVal: int)
    requires |s| >= 2
    requires minVal == min(s)
    ensures forall i :: 0 <= i < |s| ==> minVal <= s[i]
{
}

lemma ArraySliceProperty(s: array<int>)
    requires s.Length >= 2
    ensures s[..] == s[0..s.Length]
    ensures |s[..]| == s.Length
    ensures forall i :: 0 <= i < s.Length ==> s[..][i] == s[i]
{
}
// </vc-helpers>

// <vc-spec>
method SecondSmallest(s: array<int>) returns (secondSmallest: int)
    requires s.Length >= 2
    // There must be at least 2 different values, a minimum and another one
    requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] != s[i]
    ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] == secondSmallest 
    ensures forall k ::  0 <= k < s.Length && s[k] != min(s[..])  ==>  s[k] >= secondSmallest
// </vc-spec>
// <vc-code>
{
    var minVal := min(s[..]);
    MinInArray(s);
    assert exists i :: 0 <= i < s.Length && s[i] == minVal;
    
    var secondMin := s[0];
    var foundSecond := false;
    
    // Find the first element that's not the minimum
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant !foundSecond ==> forall k :: 0 <= k < i ==> s[k] == minVal
    {
        if s[i] != minVal {
            secondMin := s[i];
            foundSecond := true;
            break;
        }
        i := i + 1;
    }
    
    // Find the actual second smallest among non-minimum elements
    i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant foundSecond
        invariant exists j :: 0 <= j < s.Length && s[j] == secondMin && s[j] != minVal
        invariant forall k :: 0 <= k < i && s[k] != minVal ==> s[k] >= secondMin
    {
        if s[i] != minVal && s[i] < secondMin {
            secondMin := s[i];
        }
        i := i + 1;
    }
    
    return secondMin;
}
// </vc-code>

