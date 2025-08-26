predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a
  requires a != null
  requires from <= to
  requires to <= a.Length
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted (a:array<int>)
  reads a
  requires a!=null
{
  sorted_between (a, 0, a.Length)
}

// <vc-helpers>
lemma multiset_swap_lemma(a: array<int>, i: int, j: int, old_contents: seq<int>)
  requires a != null
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires a[..] == old_contents[i := old_contents[j]][j := old_contents[i]]
  ensures multiset(old_contents) == multiset(a[..])
{
  // Proof by extensionality - swapping two elements preserves the multiset
}

predicate largest_in_suffix(a: array<int>, pos: nat)
  reads a
  requires a != null
  requires pos < a.Length
{
  forall k :: pos <= k < a.Length ==> a[k] <= a[pos]
}

predicate max_element_at_end(a: array<int>, end: nat)
  reads a
  requires a != null
  requires end <= a.Length
{
  end > 0 ==> forall k :: 0 <= k < end ==> a[k] <= a[end-1]
}

lemma bubble_step_preserves_suffix(a_old: seq<int>, a_new: seq<int>, j: int, n: int, i: int)
  requires 0 <= j < n - 1 - i
  requires |a_old| == n && |a_new| == n
  requires sorted_between_seq(a_old, n - i, n)
  ensures sorted_between_seq(a_new, n - i, n)
{
}

predicate sorted_between_seq(s: seq<int>, from: nat, to: nat)
  requires from <= to <= |s|
{
  forall i,j :: from <= i < j < to ==> s[i] <= s[j]
}

lemma max_element_bubbles_up(a: array<int>, start: int, end: int)
  requires a != null
  requires 0 <= start < end <= a.Length
  requires forall k :: start <= k < end - 1 ==> a[k] <= a[k + 1]
  ensures forall k :: start <= k < end ==> a[k] <= a[end - 1]
{
  // The maximum element will be at the end after bubbling
}
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  modifies a
  requires a != null
  requires a.Length > 0
  ensures sorted(a)
  ensures multiset(old(a[..])) == multiset(a[..])
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant multiset(old(a[..])) == multiset(a[..])
    invariant sorted_between(a, n - i, n)
    invariant i > 0 ==> (forall k :: 0 <= k < n - i ==> a[k] <= a[n - i])
  {
    var j := 0;
    
    // Track the state at the beginning of the inner loop
    ghost var inner_start := a[..];
    
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant multiset(old(a[..])) == multiset(a[..])
      invariant multiset(inner_start) == multiset(a[..])
      invariant sorted_between(a, n - i, n)
      invariant i > 0 ==> (forall k :: 0 <= k < n - i ==> a[k] <= a[n - i])
      // Max element property: after j iterations, max of a[0..j+1] is at position j
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
    {
      if a[j] > a[j + 1] {
        var old_inner := a[..];
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
        multiset_swap_lemma(a, j, j + 1, old_inner);
      }
      j := j + 1;
    }
    
    // After inner loop, the maximum element is at position n-1-i
    assert forall k :: 0 <= k < n - i ==> a[k] <= a[n - 1 - i];
    
    i := i + 1;
  }
  
  // Final assertion to help prove sorted(a)
  assert sorted_between(a, 0, n);
}
// </vc-code>