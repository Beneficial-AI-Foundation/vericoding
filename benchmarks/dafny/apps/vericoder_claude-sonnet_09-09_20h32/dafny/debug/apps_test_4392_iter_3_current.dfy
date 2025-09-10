predicate ValidInput(a: array<int>, allowedPos: array<bool>)
    reads a, allowedPos
{
    a.Length > 1 && allowedPos.Length == a.Length
}

predicate IsSorted(a: array<int>)
    reads a
{
    forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
}

predicate CanReachConfiguration(original: seq<int>, target: seq<int>, allowed: seq<bool>)
{
    |original| == |target| == |allowed| &&
    multiset(original) == multiset(target)
}

function SortSequence(s: seq<int>): seq<int>
{
    if |s| <= 1 then s
    else
        var sorted := BubbleSortSeq(s);
        sorted
}

function BubbleSortSeq(s: seq<int>): seq<int>
{
    if |s| <= 1 then s
    else BubbleSortHelper(s, |s|)
}

function BubbleSortHelper(s: seq<int>, passes: nat): seq<int>
    decreases passes
{
    if passes == 0 then s
    else 
        var afterPass := BubblePass(s);
        BubbleSortHelper(afterPass, passes - 1)
}

function BubblePass(s: seq<int>): seq<int>
{
    if |s| <= 1 then s
    else BubblePassHelper(s, 0)
}

function BubblePassHelper(s: seq<int>, pos: nat): seq<int>
    requires pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| - 1 then s
    else if s[pos] > s[pos + 1] then
        var swapped := s[pos := s[pos + 1]][pos + 1 := s[pos]];
        BubblePassHelper(swapped, pos + 1)
    else
        BubblePassHelper(s, pos + 1)
}

// <vc-helpers>
lemma MultisetPreservedBySwap(s: seq<int>, i: int, j: int)
    requires 0 <= i < |s| && 0 <= j < |s|
    ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
{
}
// </vc-helpers>

// <vc-spec>
method CanSort(a: array<int>, allowedPos: array<bool>) returns (result: bool)
    requires ValidInput(a, allowedPos)
    modifies a
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures result == IsSorted(a)
// </vc-spec>
// <vc-code>
{
    var changed := true;
    var passes := 0;
    
    while changed && passes < a.Length
        invariant multiset(a[..]) == multiset(old(a[..]))
        decreases a.Length - passes
    {
        changed := false;
        passes := passes + 1;
        
        var i := 0;
        while i < a.Length - 1
            invariant multiset(a[..]) == multiset(old(a[..]))
            invariant 0 <= i <= a.Length - 1
        {
            if a[i] > a[i + 1] && allowedPos[i] && allowedPos[i + 1] {
                MultisetPreservedBySwap(a[..], i, i + 1);
                var temp := a[i];
                a[i] := a[i + 1];
                a[i + 1] := temp;
                changed := true;
            }
            i := i + 1;
        }
    }
    
    result := true;
    var j := 0;
    while j < a.Length - 1
        invariant 0 <= j <= a.Length - 1
        invariant result == (forall k :: 0 <= k < j ==> a[k] <= a[k + 1])
    {
        if a[j] > a[j + 1] {
            result := false;
        }
        j := j + 1;
    }
}
// </vc-code>

