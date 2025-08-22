//IMPL 
method ReverseUptoK(s: array<int>, k: int)
  modifies s
  requires 2 <= k <= s.Length
  ensures forall i :: 0 <= i < k ==> s[i] == old(s[k - 1 - i])
  ensures forall i :: k <= i < s.Length ==> s[i] == old(s[i])
{
  var left := 0;
  var right := k - 1;
  
  /* code modified by LLM (iteration 4): Simplified loop invariants to track bounds and unchanged suffix */
  while left < right
    invariant 0 <= left <= right + 1 <= k
    invariant forall i :: 0 <= i < left ==> s[i] == old(s[k - 1 - i])
    invariant forall i :: right < i < k ==> s[i] == old(s[k - 1 - i])
    invariant forall i :: k <= i < s.Length ==> s[i] == old(s[i])
  {
    var temp := s[left];
    s[left] := s[right];
    s[right] := temp;
    
    left := left + 1;
    right := right - 1;
  }
}