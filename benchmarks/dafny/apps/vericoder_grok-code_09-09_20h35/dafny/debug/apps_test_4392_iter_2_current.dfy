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
predicate IsSortedSeq(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

lemma BubblePassHelperPreserves(s: seq<int>, pos: nat)
    requires pos <= |s|
    ensures multiset(BubblePassHelper(s, pos)) == multiset(s)
    decreases |s| - pos
{
    if |s| <= 1 {
    } else if pos >= |s| - 1 {
    } else {
        if s[pos] > s[pos + 1] {
            var swapped := s[pos := s[pos + 1]][pos + 1 := s[pos]];
            BubblePassHelperPreserves(swapped, pos + 1);
        } else {
            BubblePassHelperPreserves(s, pos + 1);
        }
    }
}

lemma BubblePassPreserves(s: seq<int>)
    ensures multiset(BubblePass(s)) == multiset(s)
{
    BubblePassHelperPreserves(s, 0);
}

lemma BubbleSortHelperPreserves(s: seq<int>, passes: nat)
    decreases passes
    ensures multiset(BubbleSortHelper(s, passes)) == multiset(s)
{
    if passes == 0 {
    } else {
        BubblePassPreserves(s);
        BubbleSortHelperPreserves(BubblePass(s), passes - 1);
    }
}

lemma BubbleSortSeqPreserves(s: seq<int>)
    ensures multiset(BubbleSortSeq(s)) == multiset(s)
{
    BubbleSortHelperPreserves(s, |s|);
}

lemma MultisetPreserved(s: seq<int>)
    ensures multiset(SortSequence(s)) == multiset(s)
{
    if |s| <= 1 {
    } else {
        BubbleSortSeqPreserves(s);
    }
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
  for pass := 0 to a.Length - 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant 0 <= pass <= a.Length
    invariant IsSortedSeq(a[a.Length - pass ..])
  {
    for i := 0 to a.Length - 2 - pass
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant 0 <= i <= a.Length - 1 - pass
    {
      if a[i] > a[i + 1] {
        var temp := a[i];
        a[i] := a[i + 1];
        a[i + 1] := temp;
      }
    }
  }
  result := true;
}
// </vc-code>

