

// <vc-helpers>
lemma lemma_array_swap3_unchchanged_others(a: array<int>, h: int, i: int, j: int)
  requires 0 <= h < a.Length
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i != j && j != h && h != i
  ensures forall k: int :: 0 <= k < a.Length && k != h && k != i && k != j ==> (a[k] == old(a[k]))
{
  // This lemma is implicitly proven by the fact that the `modifies a` clause
  // in the `swap3` method only allows modification to `a`, and the
  // assignments inside the method only target a[h], a[i], and a[j].
  // Dafny's framing mechanism proves that elements not explicitly assigned
  // remain unchanged. No explicit proof steps are needed here.
}
// </vc-helpers>

// <vc-spec>
method swap3(a: array<int>, h: int, i: int, j: int)
  modifies a
  requires 0 <= h < a.Length
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i != j && j != h && h != i;
  ensures a[h] == old(a[i]);
  ensures a[j] == old(a[h]);
  ensures a[i] == old(a[j]);
  ensures forall k: int :: 0 <= k < a.Length && k != h && k != i && k != j ==> a[k] == old(a[k]);
// </vc-spec>
// <vc-code>
{
  var old_h_val := a[h];
  var old_i_val := a[i];
  var old_j_val := a[j];

  a[h] := old_i_val;
  a[j] := old_h_val;
  a[i] := old_j_val;
}
// </vc-code>

