// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)
    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]
    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && (exists j :: 0 <= j < v.Length && v[j] == result[k])
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> (exists j :: 0 <= j < result.Length && result[j] == v[k])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Switched to while loops to avoid compilation errors for empty arrays, added decreases clauses for termination proofs, and adjusted invariants for correct maintenance. */
  var count := 0;
  var i := 0;
  while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant count == |set j | 0 <= j < i && v[j] <= e|
  {
    if v[i] <= e { count := count + 1; }
    i := i + 1;
  }
  result := new int[count];
  var idx := 0;
  i := 0;
  while i < v.Length
    decreases v.Length - i
    invariant 0 <= i <= v.Length
    invariant 0 <= idx <= count
    invariant idx == |set j | 0 <= j < i && v[j] <= e|
    invariant forall k : nat :: 0 <= k < idx ==> result[k] <= e
    invariant forall k : nat :: 0 <= k < idx ==> exists j : nat :: 0 <= j < v.Length && v[j] == result[k]
    invariant forall k : nat :: 0 <= k < i && v[k] <= e ==> exists j : nat :: 0 <= j < idx && result[j] == v[k]
  {
    if v[i] <= e {
      result[idx] := v[i];
      idx := idx + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
