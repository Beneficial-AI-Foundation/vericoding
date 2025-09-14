function contains(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  exists j :: 0 <= j < n && a[j] == v
}

function upper_bound(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  forall j :: 0 <= j < n ==> a[j] <= v
}

function is_max(m: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  contains(m, a, n) && upper_bound(m, a, n)
}

// <vc-helpers>
lemma max_exists(a: array<int>, n: int)
  requires 0 < n <= a.Length
  ensures exists m :: is_max(m, a, n)
{
  if n == 1 {
    // Single element is trivially the max
    assert is_max(a[0], a, n);
  } else {
    // Recursive case: find max of first n-1 elements
    max_exists(a, n-1);
    ghost var m :| is_max(m, a, n-1);
    if m >= a[n-1] {
      assert is_max(m, a, n);
    } else {
      assert is_max(a[n-1], a, n);
    }
  }
}

lemma max_property(a: array<int>, n: int, m: int)
  requires 0 < n <= a.Length
  requires is_max(m, a, n)
  ensures contains(m, a, n) && upper_bound(m, a, n)
{
  // This is just to help Dafny understand the properties
}

lemma helper_lemma(a: array<int>, i: int, n: int, max_val: int)
  requires 0 < i <= n <= a.Length
  requires upper_bound(max_val, a, i)
  requires contains(max_val, a, i)
  ensures upper_bound(max_val, a, i)
  ensures contains(max_val, a, i)
{
  // Trivial: the preconditions already satisfy the postconditions
}

lemma update_max(a: array<int>, i: int, n: int, max_val: int)
  requires 0 < i < n <= a.Length
  requires upper_bound(max_val, a, i)
  requires contains(max_val, a, i)
  requires a[i] > max_val
  ensures upper_bound(a[i], a, i+1)
  ensures contains(a[i], a, i+1)
{
  // Show that a[i] is an upper bound for first i+1 elements
  forall j | 0 <= j < i+1
    ensures a[j] <= a[i]
  {
    if j < i {
      assert a[j] <= max_val < a[i];
    } else if j == i {
      // a[i] <= a[i] is trivially true
    }
  }
  
  // Show that a[i] is contained in first i+1 elements
  assert 0 <= i < i+1;
  assert a[i] == a[i];
}

lemma extend_upper_bound(a: array<int>, i: int, n: int, max_val: int)
  requires 0 < i <= n <= a.Length
  requires upper_bound(max_val, a, i)
  requires a[i] <= max_val
  ensures upper_bound(max_val, a, i+1)
{
  forall j | 0 <= j < i+1
    ensures a[j] <= max_val
  {
    if j < i {
      assert a[j] <= max_val;
    } else if j == i {
      assert a[j] <= max_val;
    }
  }
}

lemma extend_contains(a: array<int>, i: int, n: int, max_val: int)
  requires 0 < i <= n <= a.Length
  requires contains(max_val, a, i)
  ensures contains(max_val, a, i+1)
{
  var j :| 0 <= j < i && a[j] == max_val;
  assert 0 <= j < i+1 && a[j] == max_val;
}
// </vc-helpers>

// <vc-spec>
method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
// </vc-spec>
// <vc-code>
{
  max := a[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant contains(max, a, i)
    invariant upper_bound(max, a, i)
  {
    if a[i] > max {
      max := a[i];
      update_max(a, i, n, max);
    } else {
      extend_upper_bound(a, i, n, max);
      extend_contains(a, i, n, max);
    }
    i := i + 1;
  }
}
// </vc-code>

