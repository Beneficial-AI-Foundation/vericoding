method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function SeqToMultiset(s: seq<int>): multiset<int>
  decreases |s|
{
  if |s| == 0 then multiset{}
  else multiset{s[0]} + SeqToMultiset(s[1..])
}

lemma MultisetProperties(s: seq<int>)
  ensures multiset(s) == SeqToMultiset(s)
{
}

lemma MultisetSwap(s: seq<int>, i: int, j: int)
  requires 0 <= i < j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
}

predicate SortedByPredicate(s: seq<int>, p: seq<bool>)
  requires |s| == |p|
{
  forall i, j :: 0 <= i < j < |s| && p[i] && p[j] ==> s[i] <= s[j]
}

lemma BubbleSortStep(s: seq<int>, p: seq<bool>) returns (s': seq<int>)
  requires |s| == |p|
  ensures |s'| == |s|
  ensures multiset(s') == multiset(s)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> s'[i] == s[i]
  ensures SortedByPredicate(s', p) || (exists i :: 0 <= i < |s|-1 && p[i] && p[i+1] && s'[i] > s'[i+1])
  decreases |s|
{
  if |s| <= 1 {
    s' := s;
  } else {
    var mid := |s| / 2;
    var left := BubbleSortStep(s[..mid], p[..mid]);
    var right := BubbleSortStep(s[mid..], p[mid..]);
    
    s' := left + right;
    
    var changed := true;
    while changed
      invariant |s'| == |s|
      invariant multiset(s') == multiset(s)
      invariant forall i :: 0 <= i < |s| && !p[i] ==> s'[i] == s[i]
      decreases if changed then |s|*|s| - CountSortedPairs(s', p) else 0
    {
      changed := false;
      for k := 0 to |s'| - 2
        invariant |s'| == |s|
        invariant multiset(s') == multiset(s)
        invariant forall i :: 0 <= i < |s| && !p[i] ==> s'[i] == s[i]
        decreases |s'| - 1 - k
      {
        if p[k] && p[k+1] && s'[k] > s'[k+1] {
          s' := s'[k := s'[k+1]][k+1 := s'[k]];
          changed := true;
        }
      }
    }
  }
}

function CountSortedPairs(s: seq<int>, p: seq<bool>): int
  requires |s| == |p|
  reads s, p
{
  if |s| <= 1 then 0
  else (if p[0] && p[1] && s[0] <= s[1] then 1 else 0) + CountSortedPairs(s[1..], p[1..])
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := s;
  var changed := true;
  var pass_count := 0;
  
  while changed
    invariant |sorted| == |s|
    invariant multiset(sorted) == multiset(s)
    invariant forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
    invariant pass_count >= 0
    decreases if changed then |s|*|s| - pass_count else 0
  {
    changed := false;
    
    for i := 0 to |sorted| - 2
      invariant |sorted| == |s|
      invariant multiset(sorted) == multiset(s)
      invariant forall j :: 0 <= j < |s| && !p[j] ==> sorted[j] == s[j]
      decreases |sorted| - 1 - i
    {
      if p[i] && p[i+1] && sorted[i] > sorted[i+1] {
        sorted := sorted[i := sorted[i+1]][i+1 := sorted[i]];
        changed := true;
      }
    }
    pass_count := pass_count + 1;
  }
}
// </vc-code>

