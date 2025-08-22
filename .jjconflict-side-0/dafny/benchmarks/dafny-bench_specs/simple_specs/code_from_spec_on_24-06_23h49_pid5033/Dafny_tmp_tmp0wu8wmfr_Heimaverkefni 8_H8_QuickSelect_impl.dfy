//IMPL QuickSelect
method QuickSelect( m: multiset<int>, k: int )
    returns( pre: multiset<int>, kth: int, post: multiset<int> )
  requires 0 <= k < |m|
  ensures kth in m
  ensures m == pre + multiset{kth} + post
  ensures |pre| == k
  ensures forall z | z in pre :: z <= kth
  ensures forall z | z in post :: z >= kth
{
  var s := m;
  var arr := [];
  
  // Convert multiset to sequence
  while s != multiset{}
    decreases |s|
    /* code modified by LLM (iteration 3): added invariant to maintain relationship between arr and original multiset */
    invariant multiset(arr) + s == m
  {
    var x :| x in s;
    arr := arr + [x];
    s := s - multiset{x};
  }
  
  /* code modified by LLM (iteration 3): added assertion to establish that arr represents the original multiset */
  assert multiset(arr) == m;
  assert |arr| == |m|;
  
  // Sort the array
  arr := Sort(arr);
  
  /* code modified by LLM (iteration 3): added assertion to maintain multiset equality after sorting */
  assert multiset(arr) == m;
  assert |arr| == |m|;
  assert 0 <= k < |arr|;
  
  // The kth element (0-indexed)
  kth := arr[k];
  
  /* code modified by LLM (iteration 3): added assertion to help prove kth is in m */
  assert kth in multiset(arr);
  assert kth in m;
  
  // Build pre and post
  pre := multiset(arr[..k]);
  post := multiset(arr[k+1..]);
  
  /* code modified by LLM (iteration 3): added helper lemma calls and assertions to prove multiset decomposition */
  MultisetSliceHelper(arr, k);
  assert multiset(arr) == multiset(arr[..k]) + multiset{arr[k]} + multiset(arr[k+1..]);
  assert |arr[..k]| == k;
  assert |pre| == k;
  
  // Help prove the ordering properties
  /* code modified by LLM (iteration 3): added assertions to prove ordering properties using sorted array property */
  assert forall i, j :: 0 <= i < j < |arr| ==> arr[i] <= arr[j];
  assert forall i :: 0 <= i < k ==> arr[i] <= arr[k];
  assert forall i :: k < i < |arr| ==> arr[k] <= arr[i];
  
  /* code modified by LLM (iteration 3): added final assertions to help prove postconditions */
  OrderingHelper(arr, k);
}

/* code modified by LLM (iteration 3): added helper lemma to prove multiset slice decomposition */
lemma MultisetSliceHelper(arr: seq<int>, k: int)
  requires 0 <= k < |arr|
  ensures multiset(arr) == multiset(arr[..k]) + multiset{arr[k]} + multiset(arr[k+1..])
{
  assert arr == arr[..k] + [arr[k]] + arr[k+1..];
  assert multiset(arr[..k] + [arr[k]] + arr[k+1..]) == multiset(arr[..k]) + multiset([arr[k]]) + multiset(arr[k+1..]);
  assert multiset([arr[k]]) == multiset{arr[k]};
}

/* code modified by LLM (iteration 3): added helper lemma to prove ordering properties */
lemma OrderingHelper(arr: seq<int>, k: int)
  requires 0 <= k < |arr|
  requires forall i, j :: 0 <= i < j < |arr| ==> arr[i] <= arr[j]
  ensures forall z | z in multiset(arr[..k]) :: z <= arr[k]
  ensures forall z | z in multiset(arr[k+1..]) :: z >= arr[k]
{
  forall z | z in multiset(arr[..k])
    ensures z <= arr[k]
  {
    var i :| 0 <= i < k && arr[i] == z;
    assert arr[i] <= arr[k];
  }
  
  forall z | z in multiset(arr[k+1..])
    ensures z >= arr[k]
  {
    var j :| 0 <= j < |arr[k+1..]| && arr[k+1..][j] == z;
    assert arr[k+1+j] == z;
    assert k < k+1+j;
    assert arr[k] <= arr[k+1+j];
  }
}

/* code modified by LLM (iteration 3): simplified Sort method with better verification structure */
method Sort(arr: seq<int>) returns (sorted: seq<int>)
  ensures multiset(sorted) == multiset(arr)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
  sorted := arr;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant multiset(sorted) == multiset(arr)
    invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
    invariant forall x :: 0 <= x < i ==> forall y :: i <= y < |sorted| ==> sorted[x] <= sorted[y]
  {
    var minIdx := i;
    var j := i + 1;
    
    /* code modified by LLM (iteration 3): use selection sort for simpler verification */
    while j < |sorted|
      invariant i <= minIdx < |sorted|
      invariant i < j <= |sorted|
      invariant forall x :: i <= x < j ==> sorted[minIdx] <= sorted[x]
      invariant multiset(sorted) == multiset(arr)
    {
      if sorted[j] < sorted[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 3): swap minimum element to position i */
    if minIdx != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIdx]][minIdx := temp];
    }
    
    i := i + 1;
  }
}