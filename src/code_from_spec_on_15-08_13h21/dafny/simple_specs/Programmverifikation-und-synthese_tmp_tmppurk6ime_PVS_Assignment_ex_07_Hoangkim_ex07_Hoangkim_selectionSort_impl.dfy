method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
  requires a.Length > 0 && lo < a.Length
  ensures lo <= minIdx < a.Length
  ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
  /* code modified by LLM (iteration 1): replaced assume statements with actual implementation */
  minIdx := lo;
  var k := lo + 1;
  while k < a.Length
    invariant lo <= minIdx < a.Length
    /* code modified by LLM (iteration 1): fixed loop invariant to ensure k is within bounds */
    invariant lo + 1 <= k <= a.Length
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
  requires a.Length > 0 && i < a.Length && j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
{
  /* code modified by LLM (iteration 1): replaced incorrect assume statements with proper swap implementation */
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}


//IMPL
method selectionSort(a: array<int>)
  modifies a
  //ensures multiset(a[..]) == multiset(old(a[..]))
  //ensures sorted(a[..])
{
  /* code modified by LLM (iteration 1): removed null check since array<int> is non-null type */
  if (a.Length <= 1) {
    return;
  }
  
  var i := 0;
  /* code modified by LLM (iteration 1): added loop invariants for verification */
  while (i < a.Length)
    invariant 0 <= i <= a.Length
  {
    var minIdx := FindMin(a, i);
    if (minIdx != i) {
      swap(a, i, minIdx);
    }
    i := i + 1;
  }
}