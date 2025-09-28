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
/* helper modified by LLM (iteration 2): replaced 'function method' with 'function' for compatibility */
function Max2(x: int, y: int): int {
  if x >= y then x else y
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
  /* code modified by LLM (iteration 2): implemented linear scan to compute maximum and witness index */
  var i := 1;
  var w := 0;
  var current := a[0];
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= w < i
    invariant current == a[w]
    invariant forall k :: 0 <= k < i ==> current >= a[k]
  {
    if a[i] > current {
      current := a[i];
      w := i;
    }
    i := i + 1;
  }
  result := current;
}
// </vc-code>
