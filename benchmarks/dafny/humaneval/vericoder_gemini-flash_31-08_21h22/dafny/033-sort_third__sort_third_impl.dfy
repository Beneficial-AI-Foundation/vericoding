

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

function Sort(s: seq<int>): seq<int>
  ensures |Sort(s)| == |s|
  ensures forall i, j :: 0 <= i < j < |Sort(s)| ==> Sort(s)[i] <= Sort(s)[j]
  ensures multiset(s) == multiset(Sort(s))
{
  if |s| <= 1 then s
  else begin
    var min_val := s[0];
    var min_idx := 0;
    for i := 1 to |s|-1
      invariant 0 < i <= |s|
      invariant 0 <= min_idx < i
      invariant min_val == s[min_idx]
      invariant forall k :: 0 <= k < i ==> s[k] >= min_val
    {
      if s[i] < min_val {
        min_val := s[i];
        min_idx := i;
      }
    }
    var rest_s := s[0..min_idx] + s[min_idx+1..];
    [min_val] + Sort(rest_s)
  end
}

function IndexOf<T>(s: seq<T>, x: T): int
  requires x in s
  ensures 0 <= IndexOf(s, x) < |s|
  ensures s[IndexOf(s, x)] == x
{
  if s[0] == x then 0
  else 1 + IndexOf(s[1..], x)
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
    invariant 0 <= i <= |a|
    invariant designated_elements_indices == [k | k <- [0..i), p[k]]
    invariant forall j :: 0 <= j < |designated_elements_indices| ==> designated_elements_indices[j] < i
  {
    if p[i] {
      designated_elements_indices := designated_elements_indices + [i];
    }
  }

  var designated_elements: seq<int> := [];
  for i := 0 to |designated_elements_indices| - 1
    invariant 0 <= i <= |designated_elements_indices|
    invariant designated_elements == [a[designated_elements_indices[k]] | k <- [0..i)]
  {
    designated_elements := designated_elements + [a[designated_elements_indices[i]]];
  }

  var sorted_designated_elements := Sort(designated_elements);

  sorted_even := a; 

  var k := 0;
  for i := 0 to |a| - 1
    invariant 0 <= i <= |a|
    invariant 0 <= k <= |sorted_designated_elements|
    invariant designated_elements_indices == [idx | idx <- [0..|a|), p[idx]]
    invariant (forall j :: 0 <= j < i && p[j] ==> sorted_even[j] == sorted_designated_elements[IndexOf(designated_elements_indices, j)])
    invariant (forall j :: 0 <= j < i && !p[j] ==> sorted_even[j] == a[j])
    invariant (forall j :: i <= j < |a| ==> sorted_even[j] == a[j])
    invariant (count s | s <- designated_elements_indices, s < i) == k
    invariant multiset(a) == multiset(sorted_even)
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