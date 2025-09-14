// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed all syntax errors with proper Dafny parentheses and sequence syntax */
predicate ContainsDuplicateUpTo(seq: seq<int>, idx: int)
  requires idx >= 0
  requires |seq| >= idx
{
  exists i, j :: 0 <= i < j < idx && i < |seq| && j < |seq| && seq[i] == seq[j]
}

function FirstDuplicateIndex(seq: seq<int>): (idx: int)
  requires |seq| > 0
  requires exists i, j :: 0 <= i < j < |seq| && seq[i] == seq[j]
  ensures 0 <= idx < |seq|
  ensures exists j :: 0 <= j < idx && seq[j] == seq[idx]
  ensures forall i, j :: 0 <= i < j < idx ==> seq[i] != seq[j]
{
  if |seq| == 0 then
    0
  else if ContainsDuplicateUpTo(seq, |seq| - 1) then
    FirstDuplicateIndex(seq[0..(|seq| - 1)])
  else
    |seq| - 1
}
// </vc-helpers>

// <vc-spec>
method FirstDuplicate(lst: seq<int>) returns (result: int)
    ensures
        /* if result = -1, then lst does not contain any duplicates */
        (result == -1 ==> forall i, j :: 0 <= i < j < |lst| ==> lst[i] != lst[j]) &&
        /* if result is not -1, then it is the first duplicate in lst */
        (result != -1 ==> 
            exists i, j :: (0 <= i < j < |lst| && lst[i] == lst[j] && lst[i] == result &&
            forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i ==> k >= i))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Using recursive helper function with proper verification */
{
  if |lst| == 0 {
    result := -1;
  } else if exists i, j :: 0 <= i < j < |lst| && lst[i] == lst[j] {
    var idx := FirstDuplicateIndex(lst);
    result := lst[idx];
  } else {
    result := -1;
  }
}
// </vc-code>
