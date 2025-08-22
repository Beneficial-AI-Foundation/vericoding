// ATOM 
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

// IMPL SpMV
method SpMV(X_val: array<int>, X_crd: array<nat>, X_pos: array<nat>, v : array<int>) returns (y : array<int>)
  requires X_crd.Length >= 1 
  requires X_crd.Length == X_val.Length;
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j];
  requires forall i :: 0 <= i < X_crd.Length ==> X_crd[i] < v.Length
  requires forall i :: 0 <= i < X_pos.Length ==> X_pos[i] <= X_val.Length
  requires X_pos.Length >= 1
  ensures y.Length + 1 == X_pos.Length
  ensures forall i :: 0 <= i < y.Length ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
{
  y := new int[X_pos.Length - 1];
  
  /* code modified by LLM (iteration 1): Added comprehensive bounds checking and strengthened loop invariant */
  for i := 0 to y.Length
    invariant 0 <= i <= y.Length
    invariant y.Length == X_pos.Length - 1
    invariant forall j :: 0 <= j < i ==> y[j] == sum(X_val, X_crd, v, X_pos[j], X_pos[j + 1])
  {
    /* code modified by LLM (iteration 1): Added assertions to establish preconditions for sum function */
    assert i < y.Length;
    assert i < X_pos.Length - 1;
    assert i + 1 < X_pos.Length;
    assert 0 <= X_pos[i] <= X_pos[i + 1];
    assert X_pos[i + 1] <= X_val.Length;
    assert X_val.Length >= X_pos[i] >= 0;
    
    y[i] := sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1]);
  }
}

method Main() {
}