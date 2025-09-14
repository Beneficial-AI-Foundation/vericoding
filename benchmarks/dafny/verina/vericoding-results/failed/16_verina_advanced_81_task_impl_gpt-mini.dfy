// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): sequence-to-set function */
function SeqSet(s: seq<int>): set<int> { set x | x in s }

/* helper modified by LLM (iteration 2): lemma that inserting into a sorted sequence at index k yields a sorted sequence of length +1 */
lemma InsertPreserves(uniq: seq<int>, k: int, x: int)
  requires 0 <= k <= |uniq|
  requires forall j :: 0 <= j < |uniq| - 1 ==> uniq[j] <= uniq[j+1]
  requires forall t :: 0 <= t < k ==> uniq[t] < x
  requires forall t :: k <= t < |uniq| ==> uniq[t] >= x
  requires x !in uniq
  ensures var new := uniq[..k] + [x] + uniq[k..]; |new| == |uniq| + 1 && forall j :: 0 <= j < |new| - 1 ==> new[j] <= new[j+1]
{
  var new := uniq[..k] + [x] + uniq[k..];
  assert |new| == |uniq| + 1;
  var j := 0;
  while j < |new| - 1
    invariant 0 <= j <= |new| - 1
  {
    if j < k - 1 {
      assert new[j] == uniq[j];
      assert new[j+1] == uniq[j+1];
      assert uniq[j] <= uniq[j+1];
      assert new[j] <= new[j+1];
    } else if j == k - 1 {
      if k >= 1 {
        assert new[j] == uniq[k-1];
        assert uniq[k-1] < x;
        assert new[j+1] == x;
        assert new[j] <= new[j+1];
      }
    } else {
      assert new[j] == uniq[j-1];
      assert new[j+1] == uniq[j];
      assert uniq[j-1] <= uniq[j];
      assert new[j] <= new[j+1];
    }
    j := j + 1;
  }
}

// </vc-helpers>

// <vc-spec>
method UniqueSorted(arr: array<int>) returns (result: array<int>)
    ensures result.Length <= arr.Length
    ensures forall i :: 0 <= i < result.Length - 1 ==> result[i] <= result[i + 1]
    ensures forall x :: x in arr[..] <==> x in result[..]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build sorted unique sequence and copy to result, with helper lemma calls */
  var uniq: seq<int> := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant |uniq| <= i
    invariant forall j :: 0 <= j < |uniq| - 1 ==> uniq[j] <= uniq[j+1]
    invariant forall x :: x in arr[..i] <==> x in uniq[..]
  {
    var x := arr[i];
    if x in uniq {
      i := i + 1;
      continue;
    }
    var k := 0;
    while k < |uniq| && uniq[k] < x
      invariant 0 <= k <= |uniq|
      invariant forall t :: 0 <= t < k ==> uniq[t] < x
    {
      k := k + 1;
    }
    if k < |uniq| {
      assert uniq[k] >= x;
      assert forall t :: k <= t < |uniq| ==> uniq[t] >= x;
    } else {
      assert forall t :: k <= t < |uniq| ==> uniq[t] >= x;
    }
    InsertPreserves(uniq, k, x);
    uniq := uniq[..k] + [x] + uniq[k..];
    i := i + 1;
  }
  result := new int[|uniq|];
  var idx := 0;
  while idx < |uniq|
    invariant 0 <= idx <= |uniq|
    invariant forall j :: 0 <= j < idx ==> result[j] == uniq[j]
  {
    result[idx] := uniq[idx];
    idx := idx + 1;
  }
}

// </vc-code>
