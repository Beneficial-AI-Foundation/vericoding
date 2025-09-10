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
    CountInversionsHelper(s, 0, 0)
}

function CountInversionsHelper(s: seq<int>, i: nat, j: nat): nat
    requires i <= |s| && j <= |s|
    decreases |s| - i, |s| - j
{
    if i >= |s| - 1 then 0
    else if j <= i then CountInversionsHelper(s, i + 1, i + 2)
    else if j >= |s| then CountInversionsHelper(s, i + 1, i + 2)
    else (if s[i] > s[j] then 1 else 0) + CountInversionsHelper(s, i, j + 1)
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

lemma CountInversionsDecomposition(s: seq<int>, i: nat)
    requires i < |s| - 1
    ensures CountInversions(s) == CountInversionsBeforeI(s, i) + 
                                  (if s[i] > s[i+1] then 1 else 0) +
                                  CountInversionsAfterI(s, i) +
                                  CountCrossInversions(s, i)
{
    // The total inversions can be decomposed into:
    // 1. Inversions within s[..i]
    // 2. The inversion between s[i] and s[i+1] if it exists
    // 3. Inversions within s[i+2..]
    // 4. Cross inversions between different regions
    
    assert CountInversions(s) == CountInversionsHelper(s, 0, 0);
}

function CountInversionsBeforeI(s: seq<int>, i: nat): nat
    requires i < |s| - 1
{
    if i == 0 then 0
    else CountInversionsIn(s[..i])
}

function CountInversionsAfterI(s: seq<int>, i: nat): nat
    requires i < |s| - 1
{
    if i + 2 >= |s| then 0
    else CountInversionsIn(s[i+2..])
}

function CountCrossInversions(s: seq<int>, i: nat): nat
    requires i < |s| - 1
{
    CountCrossInversionsLeft(s, i) + CountCrossInversionsRight(s, i)
}

function CountCrossInversionsLeft(s: seq<int>, i: nat): nat
    requires i < |s| - 1
{
    CountInversionsWithPrefix(s[..i], s[i]) + CountInversionsWithPrefix(s[..i], s[i+1])
}

function CountCrossInversionsRight(s: seq<int>, i: nat): nat
    requires i < |s| - 1
{
    CountInversionsWithSuffix(s[i], s[i+2..]) + CountInversionsWithSuffix(s[i+1], s[i+2..])
}

function CountInversionsWithPrefix(prefix: seq<int>, elem: int): nat
{
    if |prefix| == 0 then 0
    else (if prefix[|prefix|-1] > elem then 1 else 0) + CountInversionsWithPrefix(prefix[..|prefix|-1], elem)
}

function CountInversionsWithSuffix(elem: int, suffix: seq<int>): nat
{
    if |suffix| == 0 then 0
    else (if elem > suffix[0] then 1 else 0) + CountInversionsWithSuffix(elem, suffix[1..])
}

function CountInversionsIn(s: seq<int>): nat
{
    CountInversions(s)
}

lemma SwapReducesInversions(s: seq<int>, i: nat)
    requires i < |s| - 1
    requires s[i] > s[i + 1]
    ensures CountInversions(s[i := s[i + 1]][i + 1 := s[i]]) < CountInversions(s)
{
    var swapped := s[i := s[i + 1]][i + 1 := s[i]];
    
    // Count inversions before and after swap
    var invBefore := CountInversions(s);
    var invAfter := CountInversions(swapped);
    
    // The swap removes exactly one inversion: the one between positions i and i+1
    assert s[i] > s[i + 1];
    assert swapped[i] == s[i + 1];
    assert swapped[i + 1] == s[i];
    assert swapped[i] <= swapped[i + 1];
    
    // All other relative orderings are preserved
    assert forall k :: 0 <= k < |s| && k != i && k != i + 1 ==> swapped[k] == s[k];
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

