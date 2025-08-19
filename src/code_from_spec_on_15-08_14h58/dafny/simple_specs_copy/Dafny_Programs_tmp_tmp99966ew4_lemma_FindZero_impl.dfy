method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
{
  var i := 0;
  
  while i < a.Length
    /* code modified by LLM (iteration 3): Added bounds check before updating i to maintain invariant */
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != 0
  {
    if a[i] == 0 {
      index := i;
      return;
    } else if a[i] > i {
      /* code modified by LLM (iteration 3): Added bounds check before skip-ahead */
      if a[i] < a.Length {
        SkipAheadLemma(a, i, a[i]);
        i := a[i];
      } else {
        /* code modified by LLM (iteration 3): Handle case where a[i] >= a.Length */
        SkipAheadLemma(a, i, a.Length);
        i := a.Length;
      }
    } else {
      i := i + 1;
    }
  }
  
  index := -1;
}

/* code modified by LLM (iteration 3): Updated lemma to handle all cases correctly */
lemma SkipAheadLemma(a: array<int>, start: int, target: int)
  requires 0 <= start < a.Length
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  requires forall j :: 0 <= j < start ==> a[j] != 0
  requires a[start] >= target
  requires target > start
  ensures forall j :: start <= j < target && j < a.Length ==> a[j] != 0
{
  /* code modified by LLM (iteration 3): Simplified proof by direct contradiction */
  var k := start;
  while k < target && k < a.Length
    invariant start <= k <= target
    invariant k <= a.Length
    invariant forall j :: start <= j < k ==> a[j] != 0
  {
    if a[k] == 0 {
      /* code modified by LLM (iteration 3): Fixed contradiction proof */
      if k == start {
        assert a[start] == 0;
        assert a[start] >= target;
        assert target > start >= 0;
        assert false; // 0 >= target > 0 is impossible
      } else {
        assert k > start;
        assert start < k < a.Length;
        MonotonicityLemma(a, start, k);
        assert a[start] <= a[k] + (k - start);
        assert a[k] == 0;
        assert a[start] <= 0 + (k - start);
        assert a[start] <= k - start;
        assert target <= a[start];
        assert target <= k - start;
        assert target + start <= k;
        assert target < k; // since target > start, we get target + start > target
        assert false; // contradiction since k < target from loop condition
      }
    }
    k := k + 1;
  }
}

/* code modified by LLM (iteration 3): Completely rewritten monotonicity lemma with proper inductive proof */
lemma MonotonicityLemma(a: array<int>, start: int, end: int)
  requires 0 <= start < end <= a.Length
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures a[start] <= a[end-1] + (end - start)
{
  /* code modified by LLM (iteration 3): Use induction from start to end-1 */
  var i := start;
  while i < end - 1
    invariant start <= i < end
    invariant a[start] <= a[i] + (i - start)
  {
    /* code modified by LLM (iteration 3): Apply the constraint a[i] - 1 <= a[i+1] */
    if i + 1 < a.Length {
      assert a[i] - 1 <= a[i + 1];
      assert a[i] <= a[i + 1] + 1;
      
      /* code modified by LLM (iteration 3): Combine with induction hypothesis */
      assert a[start] <= a[i] + (i - start);
      assert a[start] <= a[i + 1] + 1 + (i - start);
      assert a[start] <= a[i + 1] + (i + 1 - start);
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 3): At the end, i == end - 1, so we have the result */
  assert i == end - 1;
  assert a[start] <= a[i] + (i - start);
  assert a[start] <= a[end - 1] + (end - 1 - start);
  assert end - 1 - start == end - start - 1;
  
  /* code modified by LLM (iteration 3): We need a[start] <= a[end-1] + (end - start), but we have a[start] <= a[end-1] + (end - start - 1) */
  /* We need to adjust by showing that a[end-1] + (end - start - 1) <= a[end-1] + (end - start) */
  assert a[end - 1] + (end - start - 1) <= a[end - 1] + (end - start);
}