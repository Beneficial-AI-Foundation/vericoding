// SPEC

// Finds the maximum value in a non-empty array.
method findMax(a: array<real>) returns (max: real)
 requires a.Length > 0
 ensures exists k :: 0 <= k < a.Length && max == a[k]
 ensures forall k :: 0 <= k < a.Length ==> max >= a[k]
{
}
