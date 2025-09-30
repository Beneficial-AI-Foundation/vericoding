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
lemma MinProperties(s: seq<int>, i: int)
    requires |s| >= 2
    requires 0 <= i < |s|
    requires s[i] == min(s)
    ensures forall k :: 0 <= k < |s| ==> min(s) <= s[k]
{
    // This follows directly from the postcondition of min
}

lemma MinInSeq(s: seq<int>)
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
        var m := min(s[1..]);
        MinInSeq(s[1..]);
        if s[0] <= m {
            assert s[0] == min(s);
        } else {
            assert exists i :: 1 <= i < |s| && s[i] == m;
            assert m == min(s);
        }
    }
}

lemma ExistsNonMin(s: seq<int>)
    requires |s| >= 2
    requires exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] == min(s) && s[j] != s[i]
    ensures exists j :: 0 <= j < |s| && s[j] != min(s)
{
    // This follows directly from the precondition
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
    secondSmallest := minVal;
    
    var i := 0;
    var foundSecond := false;
    
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant !foundSecond ==> secondSmallest == minVal
        invariant foundSecond ==> exists j :: 0 <= j < s.Length && s[j] != minVal && s[j] == secondSmallest
        invariant foundSecond ==> secondSmallest != minVal
        invariant foundSecond ==> forall k :: 0 <= k < i && s[k] != minVal ==> s[k] >= secondSmallest
        invariant !foundSecond ==> forall k :: 0 <= k < i ==> s[k] == minVal
    {
        if s[i] != minVal {
            if !foundSecond {
                secondSmallest := s[i];
                foundSecond := true;
            } else if s[i] < secondSmallest {
                secondSmallest := s[i];
            }
        }
        i := i + 1;
    }
    
    assert foundSecond by {
        ExistsNonMin(s[..]);
        assert exists j :: 0 <= j < s.Length && s[j] != min(s[..]);
        if !foundSecond {
            assert forall k :: 0 <= k < s.Length ==> s[k] == minVal;
            assert false;
        }
    }
    
    MinInSeq(s[..]);
}
// </vc-code>

