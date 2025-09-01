

// <vc-helpers>
function make_pred_for_sort_third(len: int): (p: seq<bool>)
  ensures |p| == len
  ensures forall i :: 0 <= i < len ==> (p[i] <==> i % 3 == 0)
  decreases len
{
  if len == 0 then []
  else
    var rest := make_pred_for_sort_third(len - 1);
    rest + [ (len - 1) % 3 == 0 ]
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var p := make_pred_for_sort_third(|a|);
  var designated_elements_indices: seq<int> := [];
  for i := 0 to |a| - 1
    ensures |designated_elements_indices| <= i + 1
    ensures forall j :: 0 <= j < |designated_elements_indices| ==> designated_elements_indices[j] < i + 1
  {
    if p[i] {
      designated_elements_indices := designated_elements_indices + [i];
    }
  }

  var designated_elements: seq<int> := [];
  for i := 0 to |designated_elements_indices| - 1 {
    designated_elements := designated_elements + [a[designated_elements_indices[i]]];
  }

  // Sort the designated elements
  var sorted_designated_elements := Sort(designated_elements);

  sorted_even := a; // Initialize with 'a'

  var k := 0;
  for i := 0 to |a| - 1
    ensures |sorted_even| == |a|
    ensures k <= |sorted_designated_elements|
    ensures forall j :: 0 <= j < i ==> (p[j] ==> sorted_even[j] == (if exists l :: 0 <= l < k && designated_elements_indices[l] == j then sorted_designated_elements[l] else a[j]))
    ensures forall j :: 0 <= j < i ==> (!p[j] ==> sorted_even[j] == a[j])
  {
    if p[i] {
      sorted_even := sorted_even[i := sorted_designated_elements[k]];
      k := k + 1;
    }
  }
}
// </vc-code>

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
{
  assume{:axiom} false;
}