method ReverseUptoK(s: array<int>, k: int)
    modifies s
    requires 2 <= k <= s.Length
    ensures forall i :: 0 <= i < k ==> s[i] == old(s[k - 1 - i])
    ensures forall i :: k <= i < s.Length ==> s[i] == old(s[i])
// </vc-spec>
// <vc-code>
{
  var left := 0;
  var right := k - 1;
  
  while left < right
    invariant 0 <= left <= right + 1 <= k
    invariant forall i :: 0 <= i < left ==> s[i] == old(s[k - 1 - i])
    invariant forall i :: right < i < k ==> s[i] == old(s[k - 1 - i])
    invariant forall i :: left <= i <= right ==> s[i] == old(s[i])
    invariant forall i :: k <= i < s.Length ==> s[i] == old(s[i])
    invariant left + right == k - 1
  {
    assert k - 1 - left == right;
    assert k - 1 - right == left;
    
    var temp := s[left];
    s[left] := s[right];
    s[right] := temp;
    
    left := left + 1;
    right := right - 1;
  }
}
// </vc-code>