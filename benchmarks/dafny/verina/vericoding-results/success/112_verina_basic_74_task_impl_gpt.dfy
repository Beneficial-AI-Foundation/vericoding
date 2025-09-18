// <vc-preamble>
predicate MaxArrayPrecond(a: array<int>)
{
    a.Length > 0
}
method MaxArrayAux(a: array<int>, index: int, current: int) returns (result: int)
    requires 0 <= index <= a.Length
    decreases a.Length - index
{
    if index < a.Length {
        var new_current := if current > a[index] then current else a[index];
        result := MaxArrayAux(a, index + 1, new_current);
    } else {
        result := current;
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads frame to allow accessing array elements inside predicate */
predicate IsPrefixMax(a: array<int>, i: int, m: int, w: int)
  reads a
{
  1 <= i <= a.Length &&
  0 <= w < i &&
  m == a[w] &&
  (forall k :: 0 <= k < i ==> m >= a[k])
}
// </vc-helpers>

// <vc-spec>
method MaxArray(a: array<int>) returns (result: int)
    requires MaxArrayPrecond(a)
    ensures forall k :: 0 <= k < a.Length ==> result >= a[k]
    ensures exists k :: 0 <= k < a.Length && result == a[k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented single-pass maximum with loop invariants using IsPrefixMax */
  var m := a[0];
  var w := 0;
  var i := 1;
  while i < a.Length
    invariant IsPrefixMax(a, i, m, w)
    invariant 1 <= i <= a.Length
    decreases a.Length - i
  {
    if a[i] > m {
      m := a[i];
      w := i;
    }
    i := i + 1;
  }
  result := m;
}
// </vc-code>
