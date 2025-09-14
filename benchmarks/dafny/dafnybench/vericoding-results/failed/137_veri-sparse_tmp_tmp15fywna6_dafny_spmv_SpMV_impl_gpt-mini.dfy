function sum(X_val: array<int>, X_crd: array<nat>, v : array<int>, b : int, k : int) : (s : int)
  reads X_val, X_crd, v
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  decreases k - b
  {
    if k <= b then 
      0
    else  sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b]]
  }

// <vc-helpers>
lemma PosMono(X_pos: array<nat>, i: int)
  requires 0 <= i
  requires i + 1 < X_pos.Length
  requires forall a, b :: 0 <= a < b < X_pos.Length ==> X_pos[a] <= X_pos[b]
  ensures X_pos[i] <= X_pos[i + 1]
{
  // Direct instance of the forall hypothesis
  assert forall a, b :: 0 <= a < b < X_pos.Length ==> X_pos[a] <= X_pos[b];
  assert 0 <= i < i + 1 < X_pos.Length;
  // instantiate the forall with a := i, b := i+1
  assert X_pos[i] <= X_pos[i + 1];
}
// </vc-helpers>

// <vc-spec>
method SpMV(X_val: array<int>, X_crd: array<nat>, X_pos: array<nat>, v : array<int>) returns (y : array<int>)
  requires X_crd.Length >= 1 
  requires X_crd.Length == X_val.Length;
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j];
  requires forall i :: 0 <= i < X_crd.Length ==> X_crd[i] < v.Length
  requires forall i :: 0 <= i < X_pos.Length ==> X_pos[i] <= X_val.Length
  requires X_pos.Length >= 1
  ensures y.Length + 1 == X_pos.Length
  ensures forall i :: 0 <= i < y.Length ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
// </vc-spec>
// <vc-code>
{
  y := new int[X_pos.Length - 1];
  var n := X_pos.Length - 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> y[j] == sum(X_val, X_crd, v, X_pos[j], X_pos[j + 1])
  {
    // establish bounds for PosMono and indexing
    assert 0 <= i;
    assert n + 1 == X_pos.Length;
    assert i < n;
    assert i + 1 < X_pos.Length;
    PosMono(X_pos, i);
    assert X_pos[i + 1] <= X_val.Length;
    y[i] := sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1]);
    i := i + 1;
  }
}
// </vc-code>

// 0 0 0 0 0 0 1 0
// 0 0 0 0 0 0 0 0
// 0 0 0 0 1 0 0 0
// 0 0 0 0 0 0 0 0
// 0 0 1 0 0 0 0 0
// 0 0 0 0 0 0 0 0
// 1 0 0 0 0 0 0 0
// 0 0 0 0 0 0 0 0