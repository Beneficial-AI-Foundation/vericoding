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
lemma max_element_exists(a: array<int>, n: int)
  requires 0 < n <= a.Length
  ensures exists m :: is_max(m, a, n)
{
  var candidate := a[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] <= candidate
    invariant exists k :: 0 <= k < i && a[k] == candidate
  {
    if a[i] > candidate {
      candidate := a[i];
    }
    i := i + 1;
  }
  assert is_max(candidate, a, n);
}

lemma update_max_correct(old_max: int, new_val: int, a: array<int>, i: int)
  requires 0 <= i < a.Length
  requires a[i] == new_val
  requires forall j :: 0 <= j < i ==> a[j] <= old_max
  ensures new_val > old_max ==> 
    (forall j :: 0 <= j <= i ==> a[j] <= new_val) &&
    (exists k :: 0 <= k <= i && a[k] == new_val)
{
  if new_val > old_max {
    assert a[i] == new_val;
    assert exists k :: 0 <= k <= i && a[k] == new_val;
    
    forall j | 0 <= j <= i 
      ensures a[j] <= new_val
    {
      if j < i {
        assert a[j] <= old_max;
        assert old_max < new_val;
        assert a[j] <= new_val;
      } else {
        assert j == i;
        assert a[j] == new_val;
      }
    }
  }
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
    invariant forall j :: 0 <= j < i ==> a[j] <= max
    invariant exists k :: 0 <= k < i && a[k] == max
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
  
  assert forall j :: 0 <= j < n ==> a[j] <= max;
  assert exists k :: 0 <= k < n && a[k] == max;
  assert contains(max, a, n);
  assert upper_bound(max, a, n);
}
// </vc-code>

