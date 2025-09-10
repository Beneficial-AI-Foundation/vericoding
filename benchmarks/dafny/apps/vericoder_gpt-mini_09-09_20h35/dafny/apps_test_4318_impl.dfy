function maxHeightUpTo(heights: seq<int>, up_to_index: int): int
  requires 0 <= up_to_index < |heights|
  decreases up_to_index
{
  if up_to_index == 0 then heights[0]
  else if heights[up_to_index] >= maxHeightUpTo(heights, up_to_index - 1) then heights[up_to_index]
  else maxHeightUpTo(heights, up_to_index - 1)
}

predicate hasOceanVisibility(heights: seq<int>, mountain_index: int)
  requires 0 <= mountain_index < |heights|
{
  mountain_index == 0 || heights[mountain_index] >= maxHeightUpTo(heights, mountain_index - 1)
}

// <vc-helpers>
lemma maxHeightUpTo_extend(heights: seq<int>, k: int)
  requires 0 <= k < |heights|
  ensures k == 0 ==> maxHeightUpTo(heights, k) == heights[0]
  ensures k > 0 ==>
    (if heights[k] >= maxHeightUpTo(heights, k - 1)
     then maxHeightUpTo(heights, k) == heights[k]
     else maxHeightUpTo(heights, k) == maxHeightUpTo(heights, k - 1))
{
  if k == 0 {
    // by definition
  } else {
    var prev := maxHeightUpTo(heights, k - 1);
    if heights[k] >= prev {
      assert maxHeightUpTo(heights, k) == heights[k];
    } else {
      assert maxHeightUpTo(heights, k) == prev;
    }
  }
}

lemma ocean0_visible(heights: seq<int>)
  requires |heights| > 0
  ensures hasOceanVisibility(heights, 0)
{
  // trivial by predicate definition
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, heights: seq<int>) returns (result: int)
  requires N > 0
  requires |heights| == N
  requires N <= 20
  requires forall i :: 0 <= i < N ==> 1 <= heights[i] <= 100
  ensures 1 <= result <= N
  ensures result == |set i | 0 <= i < N && hasOceanVisibility(heights, i)|
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var curMax := heights[0];
  var k := 0;
  ghost var S: set<int> := set i | 0 <= i < 0 && hasOceanVisibility(heights, i);
  while k < N
    invariant 0 <= k <= N
    invariant 0 <= count <= k
    invariant count == |S|
    invariant S == set i | 0 <= i < k && hasOceanVisibility(heights, i)
    invariant k == 0 || curMax == maxHeightUpTo(heights, k - 1)
    invariant k == 0 ==> curMax == heights[0]
    invariant k > 0 ==> count >= 1
  {
    if k == 0 {
      // index 0 always has ocean visibility
      count := count + 1;
      S := S + {0};
    } else {
      // For k > 0, curMax == maxHeightUpTo(heights, k-1) by invariant
      if heights[k] >= curMax {
        // then k has ocean visibility
        assert curMax == maxHeightUpTo(heights, k - 1);
        assert heights[k] >= maxHeightUpTo(heights, k - 1);
        assert hasOceanVisibility(heights, k);
        count := count + 1;
        S := S + {k};
      }
    }

    // Update curMax to be the max up to index k
    if heights[k] >= curMax {
      curMax := heights[k];
    }

    // Prove that curMax == maxHeightUpTo(heights, k)
    maxHeightUpTo_extend(heights, k);
    if k == 0 {
      // help the verifier by naming the known equality
      assert curMax == heights[0];
      assert maxHeightUpTo(heights, 0) == heights[0];
      assert curMax == maxHeightUpTo(heights, 0);
    } else {
      if heights[k] >= maxHeightUpTo(heights, k - 1) {
        assert curMax == heights[k];
        assert maxHeightUpTo(heights, k) == heights[k];
      } else {
        assert curMax == maxHeightUpTo(heights, k - 1);
        assert maxHeightUpTo(heights, k) == maxHeightUpTo(heights, k - 1);
      }
      assert curMax == maxHeightUpTo(heights, k);
    }

    k := k + 1;
  }
  // After loop, k == N and invariants give count == |set i | 0 <= i < N && hasOceanVisibility(heights, i)|
  assert count == |set i | 0 <= i < N && hasOceanVisibility(heights, i)|;
  // index 0 is always visible, so count >= 1
  ocean0_visible(heights);
  assert hasOceanVisibility(heights, 0);
  // from invariants at loop end we have S == that set, and count == |S|, so show 0 in S to conclude count >= 1
  assert 0 in set i | 0 <= i < N && hasOceanVisibility(heights, i);
  assert count >= 1;
  result := count;
}
// </vc-code>

