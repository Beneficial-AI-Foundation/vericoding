predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted (a:array<int>)
  reads a;
  requires a!=null;
{
  sorted_between (a, 0, a.Length)
}

// <vc-helpers>
lemma sorted_between_extensibility(a: array<int>, from: nat, to: nat)
  requires a != null
  requires from <= to <= a.Length
  requires sorted_between(a, from, to)
  requires to < a.Length
  requires from > 0 ==> a[to-1] <= a[to]
  ensures sorted_between(a, from, to+1)
{
  if to > from {
    forall i, j | from <= i < j < to+1 && 0 <= i < j < a.Length
      ensures a[i] <= a[j]
    {
      if j < to {
        assert sorted_between(a, from, to);
      } else {
        assert j == to;
        if from > 0 {
          assert a[to-1] <= a[to];
        }
      }
    }
  }
}

lemma bubble_step_preserves_sorted_prefix(a: array<int>, i: nat, j: nat)
  requires a != null
  requires i < j < a.Length
  requires sorted_between(a, 0, j)
  requires a[i] > a[i+1]
  ensures sorted_between(a, 0, j)
{
}

lemma swap_preserves_multiset(a: array<int>, i: nat, j: nat)
  requires a != null
  requires i < a.Length && j < a.Length
  ensures multiset(old(a[..])) == multiset(a[..])
{
}

lemma bubble_inner_loop_invariant(a: array<int>, j: nat, n: nat, i: nat)
  requires a != null
  requires 0 <= j < n - i - 1
  requires n == a.Length
  requires 0 <= i < n - 1
  requires forall k :: 0 <= k < j ==> a[k] <= a[k+1]
  ensures forall k :: 0 <= k <= j ==> a[k] <= a[k+1]
{
}

lemma establish_sorted_between_after_bubble(a: array<int>, n: nat, i: nat)
  requires a != null
  requires n == a.Length
  requires 0 <= i < n - 1
  requires forall k :: 0 <= k < n - i - 1 ==> a[k] <= a[k+1]
  requires sorted_between(a, n - i, n)
  requires forall k, l :: n - i <= k < n && 0 <= l < n - i ==> a[l] <= a[k]
  ensures sorted_between(a, 0, n - i + 1)
{
  if n - i + 1 <= a.Length {
    forall p, q | 0 <= p < q < n - i + 1 && 0 <= p < q < a.Length
      ensures a[p] <= a[q]
    {
      if q < n - i {
        var mid := p;
        while mid < q - 1
          invariant p <= mid < q
          invariant a[p] <= a[mid]
        {
          assert a[mid] <= a[mid + 1];
          mid := mid + 1;
        }
        assert a[mid] <= a[q];
      } else {
        assert q >= n - i;
        assert p < n - i;
        assert a[p] <= a[q];
      }
    }
  }
}

lemma bubble_pass_establishes_max_at_end(a: array<int>, n: nat, i: nat)
  requires a != null
  requires n == a.Length
  requires 0 <= i < n - 1
  requires forall k :: 0 <= k < n - i - 1 ==> a[k] <= a[k+1]
  ensures forall k :: 0 <= k < n - i ==> a[k] <= a[n - i - 1]
{
}
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant sorted_between(a, n - i, n)
    invariant forall k, l :: n - i <= k < n && 0 <= l < n - i ==> a[l] <= a[k]
    invariant multiset(old(a[..])) == multiset(a[..])
    decreases n - 1 - i
  {
    var j := 0;
    
    while j < n - i - 1
      invariant 0 <= j <= n - i - 1
      invariant sorted_between(a, n - i, n)
      invariant forall k, l :: n - i <= k < n && 0 <= l < n - i ==> a[l] <= a[k]
      invariant forall k :: 0 <= k < j ==> a[k] <= a[k+1]
      invariant multiset(old(a[..])) == multiset(a[..])
      decreases n - i - 1 - j
    {
      if a[j] > a[j + 1] {
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
      }
      j := j + 1;
    }
    
    bubble_pass_establishes_max_at_end(a, n, i);
    establish_sorted_between_after_bubble(a, n, i);
    
    i := i + 1;
  }
}
// </vc-code>

