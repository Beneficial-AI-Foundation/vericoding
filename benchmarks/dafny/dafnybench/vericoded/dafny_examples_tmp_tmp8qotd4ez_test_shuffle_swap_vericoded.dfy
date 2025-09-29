function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method swap<T>(a: array<T>, i: int, j: int)
  // requires a != null
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}
// </vc-code>

