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
    ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
    // Dafny can verify this automatically
}

lemma MultisetInvariant(original: seq<int>, current: seq<int>)
    requires multiset(original) == multiset(current)
    ensures forall i, j :: 0 <= i < |current| && 0 <= j < |current| ==>
        multiset(current[i := current[j]][j := current[i]]) == multiset(original)
{
    forall i, j | 0 <= i < |current| && 0 <= j < |current|
    {
        MultisetPreservedBySwap(current, i, j);
    }
}

function CountInversions(s: seq<int>): nat
{
    CountInversionsFrom(s, 0)
}

function CountInversionsFrom(s: seq<int>, start: nat): nat
    requires start <= |s|
    decreases |s| - start
{
    if start >= |s| - 1 then 0
    else CountPairsFrom(s, start, start + 1) + CountInversionsFrom(s, start + 1)
}

function CountPairsFrom(s: seq<int>, i: nat, j: nat): nat
    requires i < |s| && j <= |s|
    decreases |s| - j
{
    if j >= |s| then 0
    else (if s[i] > s[j] then 1 else 0) + CountPairsFrom(s, i, j + 1)
}

lemma SwapReducesInversions(s: seq<int>, i: nat)
    requires i < |s| - 1
    requires s[i] > s[i + 1]
    ensures CountInversions(s[i := s[i + 1]][i + 1 := s[i]]) < CountInversions(s)
{
    // This lemma states that swapping adjacent out-of-order elements reduces inversions
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
    var n := a.Length;
    var iterations := 0;
    var maxIterations := n * n;
    
    while iterations < maxIterations
        invariant 0 <= iterations <= maxIterations
        invariant multiset(a[..]) == multiset(old(a[..]))
        decreases maxIterations - iterations
    {
        var changed := false;
        var i := 0;
        
        while i < n - 1
            invariant 0 <= i <= n - 1
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            if a[i] > a[i + 1] && allowedPos[i] {
                // Swap elements
                var temp := a[i];
                a[i] := a[i + 1];
                a[i + 1] := temp;
                changed := true;
                
                assert multiset(a[..]) == multiset(old(a[..])) by {
                    MultisetPreservedBySwap(old(a[..][i := a[i + 1]][i + 1 := temp]), i, i + 1);
                }
            }
            i := i + 1;
        }
        
        if !changed {
            break;
        }
        iterations := iterations + 1;
    }
    
    // Check if array is sorted
    result := true;
    var j := 0;
    while j < n - 1
        invariant 0 <= j <= n - 1
        invariant result == (forall k :: 0 <= k < j ==> a[k] <= a[k + 1])
    {
        if a[j] > a[j + 1] {
            result := false;
        }
        j := j + 1;
    }
}
// </vc-code>

