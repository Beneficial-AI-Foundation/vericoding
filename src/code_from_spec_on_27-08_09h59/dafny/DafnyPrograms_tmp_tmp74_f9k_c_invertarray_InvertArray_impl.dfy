/**
  Inverts an array of ints.
 */

// <vc-helpers>
lemma SwapPreservesInvariant(a: array<int>, old_a: seq<int>, left: int, right: int)
  requires 0 <= left < right < a.Length
  requires left + right == a.Length - 1
  requires old_a == a[..]
  requires forall i | 0 <= i < left :: a[i] == old_a[a.Length-1-i]
  requires forall i | right < i < a.Length :: a[i] == old_a[a.Length-1-i]
  requires a[left] == old_a[right] && a[right] == old_a[left]
  requires forall i | left < i < right :: a[i] == old_a[i]
  ensures forall i | 0 <= i <= left :: a[i] == old_a[a.Length-1-i]
  ensures forall i | right <= i < a.Length :: a[i] == old_a[a.Length-1-i]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if a.Length <= 1 {
    return;
  }
  
  ghost var old_a := a[..];
  var left := 0;
  var right := a.Length - 1;
  
  while left < right
    invariant 0 <= left <= right < a.Length
    invariant left + right == a.Length - 1
    invariant forall i | 0 <= i < left :: a[i] == old_a[a.Length-1-i]
    invariant forall i | right < i < a.Length :: a[i] == old_a[a.Length-1-i]
    invariant forall i | left <= i <= right :: a[i] == old_a[i]
  {
    ghost var current_a := a[..];
    
    var temp := a[left];
    a[left] := a[right];
    a[right] := temp;
    
    SwapPreservesInvariant(a, current_a, left, right);
    
    left := left + 1;
    right := right - 1;
  }
}
// </vc-code>
