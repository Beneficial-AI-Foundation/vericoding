// <vc-preamble>
function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// </vc-preamble>

// <vc-helpers>

predicate Sorted(s: seq<int>)
  ensures Sorted(s) <==> forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma PermutationLemma(s1: seq<int>, s2: seq<int>)
  requires |s1| == |s2|
  requires multiset(s1) == multiset(s2)
  ensures forall x :: x in s1 <==> x in s2
{
}

/* helper modified by LLM (iteration 5): Fixed SortedLemma to prove the correct property */
lemma SortedLemma(s: seq<int>)
  requires Sorted(s)
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
}

/* helper modified by LLM (iteration 5): Added lemma to help prove bubble sort invariants */
lemma BubbleSortInvariantHelper(sorted: seq<int>, i: int, n: int)
  requires 0 <= i < n
  requires forall k :: 0 <= k < i ==> sorted[k] <= sorted[k + 1]
  ensures forall k :: 0 <= k < i + 1 ==> sorted[k] <= sorted[i]
{
}

// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed bubble sort implementation with corrected invariants */
  sorted := s;
  var n := |s|;
  var swapped := true;
  
  while swapped
    invariant |sorted| == n
    invariant multiset(sorted) == multiset(s)
    invariant !swapped ==> Sorted(sorted)
    decreases if swapped then 1 else 0
  {
    swapped := false;
    var i := 0;
    while i < n - 1
      invariant 0 <= i <= n - 1
      invariant |sorted| == n
      invariant multiset(sorted) == multiset(s)
      invariant forall k :: 0 <= k < i ==> sorted[k] <= sorted[k + 1]
      decreases n - 1 - i
    {
      if sorted[i] > sorted[i + 1] {
        sorted := sorted[..i] + [sorted[i + 1], sorted[i]] + sorted[i + 2..];
        swapped := true;
      }
      i := i + 1;
    }
  }
  assert Sorted(sorted);
  SortedLemma(sorted);
}
// </vc-code>
