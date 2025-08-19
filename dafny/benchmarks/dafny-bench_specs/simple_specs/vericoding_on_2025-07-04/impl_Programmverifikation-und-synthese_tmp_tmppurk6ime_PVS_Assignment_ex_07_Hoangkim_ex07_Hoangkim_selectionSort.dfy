//ATOM

//b)
//Problem04
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
  requires a != null && a.Length > 0 && lo < a.Length
  ensures lo <= minIdx < a.Length
  ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
  /* code modified by LLM (iteration 2): Fixed compilation error - replaced assume with proper implementation */
  minIdx := lo;
  var k := lo + 1;
  while k < a.Length
    invariant lo <= minIdx < a.Length
    invariant lo <= k <= a.Length
    invariant forall x :: lo <= x < k ==> a[minIdx] <= a[x]
  {
    if a[k] < a[minIdx] {
      minIdx := k;
    }
    k := k + 1;
  }
}


//ATOM
//Problem01
//a)
method swap(a: array<int>, i: nat, j: nat)
  modifies a
  requires a != null && a.Length > 0 && i < a.Length && j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
  /* code modified by LLM (iteration 2): Fixed compilation error - replaced invalid assume with proper swap implementation */
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}


//IMPL selectionSort
method selectionSort(a: array<int>)
  modifies a
  //ensures multiset(a[..]) == multiset(old(a[..]))
  //ensures sorted(a[..])
{
  /* code modified by LLM (iteration 2): Fixed null check and added proper implementation */
  if a == null || a.Length <= 1 {
    return;
  }
  
  var i := 0;
  /* code modified by LLM (iteration 2): Fixed loop invariants and bounds */
  while i < a.Length - 1
    invariant 0 <= i <= a.Length - 1
    invariant forall x, y :: 0 <= x < i && i <= y < a.Length ==> a[x] <= a[y]
    invariant forall x, y :: 0 <= x < y < i ==> a[x] <= a[y]
  {
    /* code modified by LLM (iteration 2): Added assertion to ensure preconditions */
    assert i < a.Length;
    var minIdx := FindMin(a, i);
    
    /* code modified by LLM (iteration 2): Added assertions to help verification */
    assert i <= minIdx < a.Length;
    assert forall x :: i <= x < a.Length ==> a[minIdx] <= a[x];
    
    if minIdx != i {
      /* code modified by LLM (iteration 2): Added assertion before swap */
      assert i < a.Length && minIdx < a.Length;
      swap(a, i, minIdx);
    }
    i := i + 1;
  }
}