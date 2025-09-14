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
lemma UpperBound_after_update(oldm: int, a: array<int>, i: int)
  requires 0 <= i < a.Length
  requires upper_bound(oldm, a, i)
  requires a[i] > oldm
  ensures upper_bound(a[i], a, i + 1)
{
  forall j | 0 <= j < i + 1
  {
    if j < i {
      // a[j] <= oldm by upper_bound(oldm,a,i)
      assert a[j] <= oldm;
      // oldm < a[i] by assumption
      assert oldm < a[i];
      // hence a[j] <= a[i]
      assert a[j] <= a[i];
    } else {
      // j == i
      assert a[i] <= a[i];
    }
  }
}

lemma UpperBound_after_no_update(m: int, a: array<int>, i: int)
  requires 0 <= i < a.Length
  requires upper_bound(m, a, i)
  requires a[i] <= m
  ensures upper_bound(m, a, i + 1)
{
  forall j | 0 <= j < i + 1
  {
    if j < i {
      assert a[j] <= m;
    } else {
      // j == i
      assert a[i] <= m;
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
  var i := 1;
  var m := a[0];
  ghost var idx := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= idx < i
    invariant m == a[idx]
    invariant upper_bound(m, a, i)
  {
    var oldm := m;
    if a[i] > oldm {
      m := a[i];
      ghost idx := i;
      call UpperBound_after_update(oldm, a, i);
    } else {
      // m unchanged
      call UpperBound_after_no_update(m, a, i);
    }
    i := i + 1;
  }
  // prove contains(m,a,n) using idx
  assert exists j :: 0 <= j < n && a[j] == m by { witness idx; };
  max := m;
}
// </vc-code>

