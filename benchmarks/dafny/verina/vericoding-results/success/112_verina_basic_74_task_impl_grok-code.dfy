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

// </vc-helpers>

// <vc-spec>
method MaxArray(a: array<int>) returns (result: int)
    requires MaxArrayPrecond(a)
    ensures forall k :: 0 <= k < a.Length ==> result >= a[k]
    ensures exists k :: 0 <= k < a.Length && result == a[k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added loop invariants to verify postconditions */
  var max_val := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> max_val >= a[j]
    invariant exists j :: 0 <= j < i && max_val == a[j]
    decreases a.Length - i
  {
    if a[i] > max_val {
      max_val := a[i];
    }
    i := i + 1;
  }
  result := max_val;
}
// </vc-code>
