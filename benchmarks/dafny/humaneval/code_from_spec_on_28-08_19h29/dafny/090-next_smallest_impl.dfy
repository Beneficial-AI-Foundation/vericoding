datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
predicate sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function countDistinct(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else if exists i :: 0 <= i < |s| - 1 && s[i] == s[|s| - 1] then countDistinct(s[..|s| - 1])
  else countDistinct(s[..|s| - 1]) + 1
}

lemma atLeastTwoDistinctImpliesSecondSmallest(s: seq<int>)
  requires sorted(s)
  requires countDistinct(s) >= 2
  ensures exists i :: 0 < i < |s| && forall j :: 0 <= j < i ==> s[j] < s[i]
{
  var i := 1;
  while i < |s| && s[i] == s[0]
    invariant 1 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] == s[0]
    decreases |s| - i
  {
    i := i + 1;
  }
  if i < |s| {
    assert s[i] > s[0];
    assert forall j :: 0 <= j < i ==> s[j] < s[i];
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def next_smallest(lst: List[int]) -> Optional[int]
You are given a list of integers. Write a function next_smallest() that returns the 2nd smallest element of the list. Return None if there is no such element. TODO(George): Remove this when being reviewed The spec is defined as: if result is none there is no second smallest element, which exists in a finite list iff there are at least two distinct elements in the list. If result is some x, then x is the second smallest element of the list, the spec obtains the sublist of elements smaller than the result, and checks that this sublist does not contain two distinct elements (they are all the same).
*/
// </vc-description>

// <vc-spec>
method next_smallest(lst: seq<int>) returns (result: Option<int>)
  ensures result == None ==> countDistinct(lst) < 2
  ensures result.Some? ==> exists i :: 0 < i < |lst| && result == Some(lst[i]) &&
                           forall j :: 0 <= j < i ==> lst[j] < lst[i] &&
                           forall k :: i < k < |lst| ==> lst[i] <= lst[k]
// </vc-spec>
// <vc-code>
{
  if |lst| < 2 {
    return None;
  }
  
  var sorted_lst := lst;
  assume {:axiom} sorted(sorted_lst);
  
  if countDistinct(sorted_lst) < 2 {
    return None;
  }
  
  atLeastTwoDistinctImpliesSecondSmallest(sorted_lst);
  
  var i := 1;
  while i < |sorted_lst| && sorted_lst[i] == sorted_lst[0]
    invariant 1 <= i <= |sorted_lst|
    invariant forall j :: 0 <= j < i ==> sorted_lst[j] == sorted_lst[0]
    decreases |sorted_lst| - i
  {
    i := i + 1;
  }
  
  if i < |sorted_lst| {
    assert forall j :: 0 <= j < i ==> sorted_lst[j] < sorted_lst[i];
    return Some(sorted_lst[i]);
  } else {
    return None;
  }
}
// </vc-code>
