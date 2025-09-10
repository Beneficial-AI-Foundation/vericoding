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
predicate IsPermutation(a: array<int>, b: array<int>)
    reads a, b
{
    multiset(a[..]) == multiset(b[..])
}

lemma PermutationTransitive(a: array<int>, b: array<int>, c: array<int>)
    requires IsPermutation(a, b)
    requires IsPermutation(b, c)
    ensures IsPermutation(a, c)
{
    // No code needed, follows from multiset equality transitivity
}

lemma PermutationReflexive(a: array<int>)
    ensures IsPermutation(a, a)
{
    // No code needed
}

lemma PermutationSymmetric(a: array<int>, b: array<int>)
    requires IsPermutation(a, b)
    ensures IsPermutation(b, a)
{
    // No code needed
}

lemma MultisetEqualityFromSwaps(s: seq<int>, i: int, j: int)
    requires 0 <= i < |s|
    requires 0 <= j < |s|
    ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
    // A single swap preserves the multiset of elements.
    // This is a fundamental property of multisets.
}

lemma IsSortedOrCanSwap(a: array<int>, i: int)
    requires 0 <= i < a.Length - 1
    ensures a[i] <= a[i+1] || IsPermutation(a, (a[..][i := a[i+1]])[i+1 := a[i]])
{
    // If a[i] > a[i+1], we can swap them. The multiset of elements remains the same.
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

    for k := 0 to n - 1
        invariant 0 <= k <= n
        invariant IsPermutation(a, old(a))
        invariant forall i :: n - k <= i < n - 1 ==> a[i] <= a[i+1]
        decreases n - k
    {
        for i := 0 to n - k - 2
            invariant 0 <= i <= n - k - 1
            invariant IsPermutation(a, old(a))
            invariant forall j :: i + 1 <= j < n - k - 1 ==> a[j] <= a[j+1]
            invariant forall j :: 0 <= j < i ==> a[j] <= a[j+1]
            decreases (n - k - 1) - i
        {
            if a[i] > a[i+1]
            {
                var temp := a[i];
                a[i] := a[i+1];
                a[i+1] := temp;
            }
        }
    }
    result := IsSorted(a);
}
// </vc-code>

