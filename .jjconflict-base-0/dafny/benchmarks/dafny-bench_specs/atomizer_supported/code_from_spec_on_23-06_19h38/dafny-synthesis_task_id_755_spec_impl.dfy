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
    var minimum := min(s[..]);
    
    /* code modified by LLM (iteration 1): find first non-minimum value to initialize secondSmallest */
    var i := 0;
    while i < s.Length && s[i] == minimum
        invariant 0 <= i <= s.Length
        invariant forall k :: 0 <= k < i ==> s[k] == minimum
        decreases s.Length - i
    {
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): use precondition to prove element exists */
    if i == s.Length {
        // This contradicts the precondition - there must exist a non-minimum element
        assert exists idx, jdx :: 0 <= idx < s.Length && 0 <= jdx < s.Length && idx != jdx && s[idx] == minimum && s[jdx] != s[idx];
        assert false; // This should never happen given the precondition
    }
    
    assert s[i] != minimum;
    secondSmallest := s[i];
    
    /* code modified by LLM (iteration 1): now find the minimum among all non-minimum values */
    var j := 0;
    while j < s.Length
        invariant 0 <= j <= s.Length
        invariant secondSmallest != minimum
        invariant exists idx :: 0 <= idx < s.Length && s[idx] == secondSmallest
        invariant forall k :: 0 <= k < j && s[k] != minimum ==> s[k] >= secondSmallest
        decreases s.Length - j
    {
        if s[j] != minimum && s[j] < secondSmallest {
            secondSmallest := s[j];
        }
        j := j + 1;
    }
    
    /* code modified by LLM (iteration 1): establish postcondition by finding witnesses */
    ghost var minIndex: int;
    ghost var foundMin := false;
    var k := 0;
    while k < s.Length && !foundMin
        invariant 0 <= k <= s.Length
        invariant !foundMin ==> forall idx :: 0 <= idx < k ==> s[idx] != minimum  
        decreases s.Length - k
    {
        if s[k] == minimum {
            minIndex := k;
            foundMin := true;
        }
        k := k + 1;
    }
    
    ghost var secondIndex: int;
    ghost var foundSecond := false;
    k := 0;
    while k < s.Length && !foundSecond
        invariant 0 <= k <= s.Length
        invariant !foundSecond ==> forall idx :: 0 <= idx < k ==> s[idx] != secondSmallest
        decreases s.Length - k
    {
        if s[k] == secondSmallest {
            secondIndex := k;
            foundSecond := true;
        }
        k := k + 1;
    }
    
    /* code modified by LLM (iteration 1): assert witnesses satisfy postcondition */
    assert foundMin && foundSecond;
    assert s[minIndex] == minimum && s[secondIndex] == secondSmallest;
    assert minIndex != secondIndex; // since minimum != secondSmallest
}