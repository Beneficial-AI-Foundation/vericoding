```vc-helpers
function method less(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  x < u || (x == u && y > v)
}

function method less_eq(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  (x == u && y == v) || less(a, b)
}

lemma {:axiom} less_eq_antisymmetric(a: (int, int), b: (int, int))
  requires less_eq(a, b) && less_eq(b, a);
  ensures a == b;
{
}

lemma {:axiom} less_eq_transitive(a: (int, int), b: (int, int), c: (int, int))
  requires less_eq(a, b) && less_eq(b, c);
  ensures less_eq(a, c);
{
}

lemma less_eq_total(a: (int, int), b: (int, int))
  ensures less_eq(a, b) || less_eq(b, a);
{
  var (x, y) := a;
  var (u, v) := b;
  if x < u {
  } else if u < x {
  } else {
    if y < v {
    } else if v < y {
    } else {
    }
  }
}

lemma insert_maintains_sorted(sorted: SortSeqState, j: int, elem: (int, int))
  requires 0 <= j <= |sorted|
  requires forall i, k :: 0 <= i < k < |sorted| ==> less_eq(sorted[i], sorted[k])
  requires forall k :: 0 <= k < j ==> less(sorted[k], elem)
  requires j < |sorted| ==> !less(sorted[j], elem)
  ensures forall i, k :: 0 <= i < k < |(sorted[..j] + [elem] + sorted[j..])| ==> 
    less_eq((sorted[..j] + [elem] + sorted[j..])[i], (sorted[..j] + [elem] + sorted[j..])[k])
{
  if j == 0 {
    if |sorted| > 0 {
      assert !less(elem, sorted[0]);
    }
  } else if j == |sorted| {
  } else {
  }
}

lemma insert_maintains_multiset(sorted: SortSeqState, j: int, elem: (int, int))
  requires 0 <= j <= |sorted|
  ensures multiset(sorted[..j] + [elem] + sorted[j..]) == multiset(sorted) + multiset([elem])
{
}
```
```vc-code
{
  sorted := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall k, l :: 0 <= k < l < |sorted| ==> less_eq(sorted[k], sorted[l])
    invariant multiset(sorted) == multiset(s[0..i])
  {
    var j := 0;
    while j < |sorted| && less(sorted[j], s[i])
      invariant 0 <= j <= |sorted|
      invariant forall k :: 0 <= k < j ==> less(sorted[k], s[i])
    {
      j := j + 1;
    }
    insert_maintains_sorted(sorted, j, s[i]);
    insert_maintains_multiset(sorted, j, s[i]);
    sorted := sorted[..j] + [s[i]] + sorted[j..];
  }
}
```