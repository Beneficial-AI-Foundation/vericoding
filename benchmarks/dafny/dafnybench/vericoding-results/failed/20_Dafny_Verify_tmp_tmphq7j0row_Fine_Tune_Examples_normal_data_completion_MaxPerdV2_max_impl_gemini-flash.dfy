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
lemma max_is_upper_bound(a: array<int>, n: int, m: int)
  requires 0 < n <= a.Length
  requires forall k :: 0 <= k < n ==> a[k] <= m
  ensures upper_bound(m, a, n)
{
  // The postcondition is exactly the requirement, so this lemma is trivial.
  // It's here mainly for illustrative purposes if further proofs were needed.
}

lemma max_contains_element(a: array<int>, n: int, m: int)
  requires 0 < n <= a.Length
  requires exists k :: 0 <= k < n && a[k] == m
  ensures contains(m, a, n)
{
  // The postcondition is exactly the requirement, so this lemma is trivial.
}
// </vc-helpers>

// <vc-spec>
method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
// </vc-spec>
// <vc-code>
{
  var max_val := a[0];
  var i := 1;
  while i < n
    invariant 0 < n <= a.Length
    invariant 0 <= i <= n
    invariant (exists k :: 0 <= k < i && a[k] == max_val) || (i==0 && max_val == a[0])
    invariant (forall k :: 0 <= k < i ==> a[k] <= max_val)
  {
    if a[i] > max_val {
      max_val := a[i];
    }
    i := i + 1;
  }
  max := max_val;
}
// </vc-code>

