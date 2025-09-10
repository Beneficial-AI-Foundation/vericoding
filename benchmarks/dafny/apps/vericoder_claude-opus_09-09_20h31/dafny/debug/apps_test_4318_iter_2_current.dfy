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
lemma SetCardinalityUpTo(heights: seq<int>, k: int)
  requires 0 <= k <= |heights|
  ensures |set i | 0 <= i < k && hasOceanVisibility(heights, i)| >= 0
  ensures k == 0 ==> |set i | 0 <= i < k && hasOceanVisibility(heights, i)| == 0
{
  if k == 0 {
    assert (set i | 0 <= i < k && hasOceanVisibility(heights, i)) == {};
  }
}

lemma SetExtension(heights: seq<int>, k: int)
  requires 0 < k <= |heights|
  ensures (set i | 0 <= i < k && hasOceanVisibility(heights, i)) ==
          (set i | 0 <= i < k-1 && hasOceanVisibility(heights, i)) +
          (if hasOceanVisibility(heights, k-1) then {k-1} else {})
{
  var S1 := set i | 0 <= i < k && hasOceanVisibility(heights, i);
  var S2 := set i | 0 <= i < k-1 && hasOceanVisibility(heights, i);
  var S3 := if hasOceanVisibility(heights, k-1) then {k-1} else {};
  
  forall x | x in S1
  ensures x in S2 + S3
  {
    if x == k-1 {
      assert hasOceanVisibility(heights, k-1);
      assert x in S3;
    } else {
      assert 0 <= x < k-1;
      assert x in S2;
    }
  }
  
  forall x | x in S2 + S3
  ensures x in S1
  {
    if x in S2 {
      assert 0 <= x < k-1;
      assert x in S1;
    } else {
      assert x in S3;
      assert x == k-1;
      assert hasOceanVisibility(heights, k-1);
      assert x in S1;
    }
  }
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
  var max_so_far := 0;
  var k := 0;
  
  while k < N
    invariant 0 <= k <= N
    invariant 0 <= count <= k
    invariant count == |set i | 0 <= i < k && hasOceanVisibility(heights, i)|
    invariant k > 0 ==> max_so_far == maxHeightUpTo(heights, k - 1)
  {
    SetCardinalityUpTo(heights, k);
    
    if k == 0 || heights[k] >= max_so_far {
      count := count + 1;
      
      SetExtension(heights, k + 1);
      assert hasOceanVisibility(heights, k);
      var S_old := set i | 0 <= i < k && hasOceanVisibility(heights, i);
      var S_new := set i | 0 <= i < k + 1 && hasOceanVisibility(heights, i);
      assert S_new == S_old + {k};
      assert k !in S_old;
      assert |S_new| == |S_old| + 1;
    } else {
      SetExtension(heights, k + 1);
      assert !hasOceanVisibility(heights, k);
      var S_old := set i | 0 <= i < k && hasOceanVisibility(heights, i);
      var S_new := set i | 0 <= i < k + 1 && hasOceanVisibility(heights, i);
      assert S_new == S_old;
    }
    
    if k == 0 {
      max_so_far := heights[0];
    } else if heights[k] > max_so_far {
      max_so_far := heights[k];
    }
    
    k := k + 1;
  }
  
  assert k == N;
  result := count;
}
// </vc-code>

