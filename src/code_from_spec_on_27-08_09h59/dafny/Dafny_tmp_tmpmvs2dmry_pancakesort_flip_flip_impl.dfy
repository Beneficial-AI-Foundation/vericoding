// flips (i.e., reverses) array elements in the range [0..num]

// <vc-helpers>
lemma SwapPreservesOtherElements(a: array<int>, i: int, j: int, old_a: seq<int>)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires old_a == a[..]
  requires a[..] == old_a[i := old_a[j]][j := old_a[i]]
  ensures forall k :: k != i && k != j && 0 <= k < a.Length ==> a[k] == old_a[k]
{
}

lemma FlipInvariant(a: array<int>, num: int, left: int, old_a: seq<int>)
  requires 0 <= num < a.Length
  requires 0 <= left <= num/2 + 1
  requires old_a == a[..]
  requires forall k :: 0 <= k < left ==> a[k] == old_a[num-k]
  requires forall k :: num-left < k <= num ==> a[k] == old_a[num-k]
  requires forall k :: left <= k <= num-left ==> a[k] == old_a[k]
  requires forall k :: num < k < a.Length ==> a[k] == old_a[k]
  ensures left > num/2 ==> (forall k :: 0 <= k <= num ==> a[k] == old_a[num-k])
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method flip (a: array<int>, num: int)
requires a.Length > 0;
requires 0 <= num < a.Length;
modifies a;
ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k])
ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
// ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if num == 0 {
    return;
  }
  
  ghost var old_a := a[..];
  var left := 0;
  var right := num;
  
  while left < right
    invariant 0 <= left <= right + 1
    invariant right <= num
    invariant left + right == num
    invariant forall k :: 0 <= k < left ==> a[k] == old_a[num-k]
    invariant forall k :: right < k <= num ==> a[k] == old_a[num-k]
    invariant forall k :: left <= k <= right ==> a[k] == old_a[k]
    invariant forall k :: num < k < a.Length ==> a[k] == old_a[k]
  {
    var temp := a[left];
    a[left] := a[right];
    a[right] := temp;
    
    left := left + 1;
    right := right - 1;
  }
}
// </vc-code>
