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
lemma sum_bound_lemma(X_val: array<int>, X_crd: array<nat>, v : array<int>, b : int, k : int)
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  ensures b <= k || k <= b
{
}

lemma sum_equal_lemma(X_val: array<int>, X_crd: array<nat>, v : array<int>, b : int, k : int)
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  ensures sum(X_val, X_crd, v, b, k) == sum(X_val, X_crd, v, b, k)
{
}

lemma pos_ordering_lemma(X_pos: array<nat>, i: int)
  requires forall j, k :: 0 <= j < k < X_pos.Length ==> X_pos[j] <= X_pos[k]
  requires 0 <= i < X_pos.Length - 1
  ensures X_pos[i] <= X_pos[i + 1]
{
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
  
  var i := 0;
  while i < y.Length
    invariant 0 <= i <= y.Length
    invariant forall j :: 0 <= j < i ==> y[j] == sum(X_val, X_crd, v, X_pos[j], X_pos[j + 1])
  {
    pos_ordering_lemma(X_pos, i);
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