//Problem01
//a)

//b)
//Problem04

method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
  assume{:axiom} false;
}

//Problem02
ghost predicate sorted(a:seq<int>)
{
    forall i | 0 < i < |a| :: a[i-1] <= a[i]     
}

// <vc-helpers>
ghost predicate sorted_array(a: array<int>) {
  (a.Length == 0 || forall i | 0 <= i < a.Length - 1 :: a[i] <= a[i+1])
}

predicate sorted(s: seq<int>) {
  forall i :: 0 < i < |s| ==> s[i-1] <= s[i]
}

lemma sorted_array_to_sorted_seq(a: array<int>)
  requires sorted_array(a)
  ensures sorted(a[..])
{}

lemma sorted_seq_to_sorted_array(s: seq<int>)
  requires sorted(s)
  ensures sorted_array(s[..])
{}
// </vc-helpers>

// <vc-spec>
method selectionSort(a: array<int>)
    modifies a
    //ensures multiset(a[..]) == multiset(old(a[..]))
    //ensures sorted(a[..])
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  if n == 0 { return; }

  for i := 0 to n-1
    invariant 0 <= i <= n
    invariant forall x, y :: 0 <= x < i && i <= y < n ==> a[x] <= a[y]
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k | 0 <= k < i :: (exists old_k | 0 <= old_k < old(a.Length) :: a[k] == old(a[old_k]))
    invariant forall k | i <= k < n :: (exists old_k | 0 <= old_k < old(a.Length) :: a[k] == old(a[old_k]))
    invariant sorted_array(a[0..i])
  {
    if i == n - 1 { break; } 
    var minIdx := i;
    for j := i + 1 to n - 1
      invariant i <= minIdx < j
      invariant forall k :: i <= k < j ==> a[minIdx] <= a[k]
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall k | 0 <= k < n :: (exists old_k | 0 <= old_k < old(a.Length) :: a[k] == old(a[old_k]))
    {
      if a[j] < a[minIdx] {
        minIdx := j;
      }
    }

    if minIdx != i {
      var temp := a[i];
      a[i] := a[minIdx];
      a[minIdx] := temp;
    }
  }
  assert sorted_array(a);
}
// </vc-code>

//Problem03