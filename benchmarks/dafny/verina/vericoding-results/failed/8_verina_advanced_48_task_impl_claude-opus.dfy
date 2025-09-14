// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemmas to prove merge correctness */
function Merge(left: seq<int>, right: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |left| ==> left[i] <= left[j]
  requires forall i, j :: 0 <= i < j < |right| ==> right[i] <= right[j]
  ensures |Merge(left, right)| == |left| + |right|
  ensures forall i, j :: 0 <= i < j < |Merge(left, right)| ==> Merge(left, right)[i] <= Merge(left, right)[j]
  ensures multiset(Merge(left, right)) == multiset(left) + multiset(right)
  decreases |left| + |right|
{
  if |left| == 0 then right
  else if |right| == 0 then left
  else if left[0] <= right[0] then
    MergeLeftFirst(left, right)
  else
    MergeRightFirst(left, right)
}

function MergeLeftFirst(left: seq<int>, right: seq<int>): seq<int>
  requires |left| > 0
  requires forall i, j :: 0 <= i < j < |left| ==> left[i] <= left[j]
  requires forall i, j :: 0 <= i < j < |right| ==> right[i] <= right[j]
  requires |right| == 0 || left[0] <= right[0]
  ensures |MergeLeftFirst(left, right)| == |left| + |right|
  ensures forall i, j :: 0 <= i < j < |MergeLeftFirst(left, right)| ==> MergeLeftFirst(left, right)[i] <= MergeLeftFirst(left, right)[j]
  ensures multiset(MergeLeftFirst(left, right)) == multiset(left) + multiset(right)
  decreases |left| + |right|
{
  var tail := Merge(left[1..], right);
  MergeLeftLemma(left, right, tail);
  [left[0]] + tail
}

function MergeRightFirst(left: seq<int>, right: seq<int>): seq<int>
  requires |right| > 0
  requires forall i, j :: 0 <= i < j < |left| ==> left[i] <= left[j]
  requires forall i, j :: 0 <= i < j < |right| ==> right[i] <= right[j]
  requires |left| == 0 || right[0] < left[0]
  ensures |MergeRightFirst(left, right)| == |left| + |right|
  ensures forall i, j :: 0 <= i < j < |MergeRightFirst(left, right)| ==> MergeRightFirst(left, right)[i] <= MergeRightFirst(left, right)[j]
  ensures multiset(MergeRightFirst(left, right)) == multiset(left) + multiset(right)
  decreases |left| + |right|
{
  var tail := Merge(left, right[1..]);
  MergeRightLemma(left, right, tail);
  [right[0]] + tail
}

lemma MergeLeftLemma(left: seq<int>, right: seq<int>, tail: seq<int>)
  requires |left| > 0
  requires forall i, j :: 0 <= i < j < |left| ==> left[i] <= left[j]
  requires forall i, j :: 0 <= i < j < |right| ==> right[i] <= right[j]
  requires |right| == 0 || left[0] <= right[0]
  requires tail == Merge(left[1..], right)
  requires |tail| == |left[1..]| + |right|
  requires forall i, j :: 0 <= i < j < |tail| ==> tail[i] <= tail[j]
  requires multiset(tail) == multiset(left[1..]) + multiset(right)
  ensures forall i, j :: 0 <= i < j < |[left[0]] + tail| ==> ([left[0]] + tail)[i] <= ([left[0]] + tail)[j]
  ensures multiset([left[0]] + tail) == multiset(left) + multiset(right)
{
  assert multiset([left[0]]) + multiset(left[1..]) == multiset(left);
  assert multiset([left[0]] + tail) == multiset([left[0]]) + multiset(tail);
  assert multiset([left[0]] + tail) == multiset([left[0]]) + multiset(left[1..]) + multiset(right);
  
  forall i, j | 0 <= i < j < |[left[0]] + tail|
    ensures ([left[0]] + tail)[i] <= ([left[0]] + tail)[j]
  {
    if i == 0 {
      if j == 1 {
        if |tail| > 0 {
          assert tail[0] >= left[0] by {
            if |left[1..]| > 0 {
              assert left[1..][0] == left[1];
              assert left[0] <= left[1];
            }
            if |right| > 0 {
              assert left[0] <= right[0];
            }
          }
        }
      }
    }
  }
}

lemma MergeRightLemma(left: seq<int>, right: seq<int>, tail: seq<int>)
  requires |right| > 0
  requires forall i, j :: 0 <= i < j < |left| ==> left[i] <= left[j]
  requires forall i, j :: 0 <= i < j < |right| ==> right[i] <= right[j]
  requires |left| == 0 || right[0] < left[0]
  requires tail == Merge(left, right[1..])
  requires |tail| == |left| + |right[1..]|
  requires forall i, j :: 0 <= i < j < |tail| ==> tail[i] <= tail[j]
  requires multiset(tail) == multiset(left) + multiset(right[1..])
  ensures forall i, j :: 0 <= i < j < |[right[0]] + tail| ==> ([right[0]] + tail)[i] <= ([right[0]] + tail)[j]
  ensures multiset([right[0]] + tail) == multiset(left) + multiset(right)
{
  assert multiset([right[0]]) + multiset(right[1..]) == multiset(right);
  assert multiset([right[0]] + tail) == multiset([right[0]]) + multiset(tail);
  assert multiset([right[0]] + tail) == multiset(left) + multiset([right[0]]) + multiset(right[1..]);
  
  forall i, j | 0 <= i < j < |[right[0]] + tail|
    ensures ([right[0]] + tail)[i] <= ([right[0]] + tail)[j]
  {
    if i == 0 {
      if j == 1 {
        if |tail| > 0 {
          assert tail[0] >= right[0] by {
            if |left| > 0 {
              assert right[0] < left[0];
            }
            if |right[1..]| > 0 {
              assert right[1..][0] == right[1];
              assert right[0] <= right[1];
            }
          }
        }
      }
    }
  }
}

function MergeSortHelper(list: seq<int>): seq<int>
  ensures |MergeSortHelper(list)| == |list|
  ensures forall i, j :: 0 <= i < j < |MergeSortHelper(list)| ==> MergeSortHelper(list)[i] <= MergeSortHelper(list)[j]
  ensures multiset(MergeSortHelper(list)) == multiset(list)
  decreases |list|
{
  if |list| <= 1 then list
  else
    var mid := |list| / 2;
    var left := MergeSortHelper(list[..mid]);
    var right := MergeSortHelper(list[mid..]);
    assert multiset(list[..mid]) + multiset(list[mid..]) == multiset(list);
    Merge(left, right)
}
// </vc-helpers>

// <vc-spec>
method MergeSort(list: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |list| &&
        (forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]) &&
        multiset(result) == multiset(list)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simple delegation to helper function */
{
  result := MergeSortHelper(list);
}
// </vc-code>
