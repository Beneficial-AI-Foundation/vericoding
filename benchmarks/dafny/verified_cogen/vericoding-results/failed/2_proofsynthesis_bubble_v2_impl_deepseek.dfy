// <vc-preamble>
predicate SortedBetween(a: seq<int>, from: int, to: int)
{
    forall i, j :: from <= i < j < to && 0 <= i < |a| && 0 <= j < |a| ==> a[i] <= a[j]
}

predicate IsReorderOf<T(==)>(r: seq<int>, p: seq<T>, s: seq<T>)
{
    && |r| == |s|
    && (forall i :: 0 <= i < |r| ==> 0 <= r[i] < |r|)
    && (forall i, j :: 0 <= i < j < |r| ==> r[i] != r[j])
    && p == seq(|r|, i requires 0 <= i < |r| => s[r[i]])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix result identifier and compilation errors */
function FindMinInSegment(a: seq<int>, from: int, to: int): (result: int)
  requires 0 <= from < to <= |a|
  ensures from <= result < to
  ensures forall k :: from <= k < to ==> a[result] <= a[k]
{
  if to - from == 1 then
    from
  else
    var minIndexRest := FindMinInSegment(a, from + 1, to);
    if a[from] < a[minIndexRest] then from else minIndexRest
}

lemma SelectionSortLemma(a: seq<int>, from: int, to: int)
  requires 0 <= from <= to <= |a|
  ensures exists r: seq<int> :: IsReorderOf(r, a, a) && SortedBetween(a, from, to)
{
  if from >= to - 1 {
    var identity := seq(|a|, i requires 0 <= i < |a| => i);
    assert IsReorderOf(identity, a, a);
    assert SortedBetween(a, from, to);
  } else {
    var minIndex := FindMinInSegment(a, from, to);
    var swapped := a[from := a[minIndex]][minIndex := a[from]];
    SelectionSortLemma(swapped, from + 1, to);
  }
}
// </vc-helpers>

// <vc-spec>
method Test1(nums: array<int>)
    modifies nums
    ensures SortedBetween(nums[..], 0, nums.Length)
    ensures exists r :: IsReorderOf(r, nums[..], old(nums[..]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Remove while loop invariants and simplify to bubble sort implementation */
  var old_vals := nums[..];
  var n := nums.Length;
  
  if n > 1 {
    var i := 0;
    while i < n - 1
      decreases n - 1 - i
    {
      var j := n - 1;
      while j > i
        decreases j - i
      {
        if nums[j - 1] > nums[j] {
          var temp := nums[j - 1];
          nums[j - 1] := nums[j];
          nums[j] := temp;
        }
        j := j - 1;
      }
      i := i + 1;
    }
  }
  
  assert SortedBetween(nums[..], 0, nums.Length);
  assert exists r :: IsReorderOf(r, nums[..], old_vals);
}
// </vc-code>
