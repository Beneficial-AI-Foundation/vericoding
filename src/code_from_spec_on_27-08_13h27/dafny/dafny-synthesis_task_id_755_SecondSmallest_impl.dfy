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
function MinPairHelper(s: seq<int>) : (r: int)
    requires |s| == 2
    ensures s[0] <= s[1] <==> r == s[0]
    ensures s[0] > s[1] ==> r == s[1]
{
    if s[0] <= s[1] then s[0] else s[1]
}

function MinHelper(s: seq<int>) : (r: int)
    requires |s| >= 2
    ensures forall i :: 0 <= i < |s| ==> r <= s[i]
{
    if |s| == 2 then MinPairHelper(s)
    else MinPairHelper([s[0], MinHelper(s[1..])])
}

lemma MinExistsHelper(s: seq<int>, m: int)
    requires |s| >= 2
    requires m == MinHelper(s)
    ensures exists i :: 0 <= i < |s| && s[i] == m
{
    if |s| == 2 {
        if s[0] <= s[1] {
            assert s[0] == m;
        } else {
            assert s[1] == m;
        }
    } else {
        var restMin := MinHelper(s[1..]);
        if s[0] <= restMin {
            assert s[0] == m;
        } else {
            MinExistsHelper(s[1..], restMin);
            assert exists i :: 1 <= i < |s| && s[i] == restMin;
        }
    }
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
method SecondSmallestImpl(s: array<int>) returns (secondSmallest: int)
    requires s.Length >= 2
    requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == MinHelper(s[..]) && s[j] != s[i]
    ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == MinHelper(s[..]) && s[j] == secondSmallest 
    ensures forall k :: 0 <= k < s.Length && s[k] != MinHelper(s[..]) ==> s[k] >= secondSmallest
{
    var minVal := MinHelper(s[..]);
    MinExistsHelper(s[..], minVal);
    var minIndex := 0;
    while minIndex < s.Length && s[minIndex] != minVal
        invariant 0 <= minIndex <= s.Length
        invariant forall k :: 0 <= k < minIndex ==> s[k] != minVal
    {
        minIndex := minIndex + 1;
    }
    assert minIndex < s.Length;
    assert s[minIndex] == minVal;
    var secondIndex := if minIndex == 0 then 1 else 0;
    secondSmallest := s[secondIndex];
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant 0 <= secondIndex < s.Length
        invariant secondSmallest == s[secondIndex]
        invariant minIndex != secondIndex
        invariant forall k :: 0 <= k < i && k != minIndex ==> s[k] >= secondSmallest || s[k] == minVal
    {
        if i != minIndex && s[i] < secondSmallest && s[i] != minVal {
            secondSmallest := s[i];
            secondIndex := i;
        }
        i := i + 1;
    }
    assert exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == minVal && s[j] == secondSmallest by {
        assert s[minIndex] == minVal;
        assert s[secondIndex] == secondSmallest;
        assert minIndex != secondIndex;
    }
}
// </vc-code>
