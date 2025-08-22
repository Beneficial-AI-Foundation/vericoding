//IMPL 
method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{
  if a.Length <= 1 {
    return;
  }
  
  var left := 0;
  var right := a.Length - 1;
  
  /* code modified by LLM (iteration 3): Fixed invariants to properly track the reversal property with correct swapped element relationships */
  while left < right
    invariant 0 <= left <= right + 1 <= a.Length
    invariant forall i :: 0 <= i < left ==> a[i] == old(a[a.Length - 1 - i])
    invariant forall i :: right < i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
    invariant forall i :: left <= i <= right ==> a[i] == old(a[i])
    invariant left + right == a.Length - 1
  {
    var temp := a[left];
    a[left] := a[right];
    a[right] := temp;
    
    left := left + 1;
    right := right - 1;
  }
}