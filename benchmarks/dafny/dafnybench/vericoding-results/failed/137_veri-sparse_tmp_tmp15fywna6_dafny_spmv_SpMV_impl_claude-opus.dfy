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
lemma SumLemma(X_val: array<int>, X_crd: array<nat>, v: array<int>, b: int, k: int)
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  ensures b < k ==> sum(X_val, X_crd, v, b, k) == sum(X_val, X_crd, v, b, k-1) + X_val[k-1] * v[X_crd[k-1]]
  decreases k - b
{
  if b >= k {
    return;
  }
  if k == b + 1 {
    assert sum(X_val, X_crd, v, b, k) == X_val[b] * v[X_crd[b]];
    assert sum(X_val, X_crd, v, b, k-1) == 0;
  } else {
    SumLemma(X_val, X_crd, v, b+1, k);
  }
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
    var row_sum := 0;
    var k := X_pos[i];
    
    while k < X_pos[i + 1]
      invariant X_pos[i] <= k <= X_pos[i + 1]
      invariant k <= X_val.Length
      invariant row_sum == sum(X_val, X_crd, v, X_pos[i], k)
      invariant i + 1 < X_pos.Length
      invariant forall j :: 0 <= j < i ==> y[j] == sum(X_val, X_crd, v, X_pos[j], X_pos[j + 1])
    {
      row_sum := row_sum + X_val[k] * v[X_crd[k]];
      SumLemma(X_val, X_crd, v, X_pos[i], k + 1);
      k := k + 1;
    }
    
    y[i] := row_sum;
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