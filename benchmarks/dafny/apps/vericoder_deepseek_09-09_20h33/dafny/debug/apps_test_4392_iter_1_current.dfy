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
lemma SwappedBubbleSortHelper(s: seq<int>, passes: nat, i: int)
    requires 0 <= i < passes
    requires passes <= |s|
{
}

lemma SwapInBubblePassHelper(s: seq<int>, pos: nat)
    requires pos < |s| - 1
{
    if s[pos] > s[pos + 1] {
        var swapped := s[pos := s[pos + 1]][pos + 1 := s[pos]];
    }
}

lemma BubbleSortHelperSorted(s: seq<int>, passes: nat)
    requires passes >= |s|
    ensures IsSortedSeq(BubbleSortHelper(s, passes))
{
}

predicate IsSortedSeq(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

lemma BubblePreservesMultiset(s: seq<int>, passes: nat)
    ensures multiset(BubbleSortHelper(s, passes)) == multiset(s)
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
  var n := a.Length;
  var i := n;
  
  while i > 0
    invariant 0 <= i <= n
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases i
  {
    var j := 0;
    while j < n - 1
      invariant 0 <= j <= n - 1
      invariant multiset(a[..]) == multiset(old(a[..]))
      decreases n - 1 - j
    {
      if allowedPos[j] && !allowedPos[j + 1] {
        // Cannot swap if j is allowed but j+1 is not
        j := j + 1;
      } else if !allowedPos[j] && allowedPos[j + 1] {
        // Cannot swap if j is not allowed but j+1 is allowed
        j := j + 1;
      } else if allowedPos[j] && allowedPos[j + 1] && a[j] > a[j + 1] {
        // Only swap if both positions are allowed and out of order
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
        j := j + 1;
      } else {
        j := j + 1;
      }
    }
    i := i - 1;
  }
  
  result := IsSorted(a);
}
// </vc-code>

