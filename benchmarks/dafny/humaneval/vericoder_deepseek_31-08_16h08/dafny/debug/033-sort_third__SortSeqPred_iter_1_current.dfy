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
function method SeqToMultiset(s: seq<int>): multiset<int>
{
  if |s| == 0 then multiset{}
  else multiset{s[0]} + SeqToMultiset(s[1..])
}

lemma MultisetProperties(s: seq<int>)
  ensures multiset(s) == SeqToMultiset(s)
  ensures forall x :: x in s ==> x in multiset(s)
  ensures forall x :: x in multiset(s) ==> x in s
{
}

lemma MultisetUpdatePreserved(s: seq<int>, i: int, j: int, val: int)
  requires 0 <= i <= j < |s|
  ensures multiset(s[i := val][j := s[i]]) == multiset(s)
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
      decreases |s| * |s| - count
    {
      changed := false;
      for k := 0 to |s'| - 2
        invariant |s'| == |s|
        invariant multiset(s') == multiset(s)
        invariant forall i :: 0 <= i < |s| && !p[i] ==> s'[i] == s[i]
      {
        if p[k] && p[k+1] && s'[k] > s'[k+1] {
          s' := s'[k := s'[k+1]][k+1 := s'[k]];
          changed := true;
        }
      }
    }
  }
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
  sorted_even := a;
  var changed := true;
  
  while changed
    invariant |sorted_even| == |a|
    invariant multiset(sorted_even) == multiset(a)
    invariant forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
    decreases |a| * |a| - count
  {
    changed := false;
    
    for i := 0 to |a| - 4
      invariant |sorted_even| == |a|
      invariant multiset(sorted_even) == multiset(a)
      invariant forall j :: 0 <= j < |a| && j % 3 != 0 ==> sorted_even[j] == a[j]
    {
      var j := i + 3;
      if i % 3 == 0 && j < |a| && j % 3 == 0 && sorted_even[i] > sorted_even[j] {
        var temp := sorted_even[i];
        sorted_even := sorted_even[i := sorted_even[j]];
        sorted_even := sorted_even[j := temp];
        changed := true;
      }
    }
  }
}
// </vc-code>

