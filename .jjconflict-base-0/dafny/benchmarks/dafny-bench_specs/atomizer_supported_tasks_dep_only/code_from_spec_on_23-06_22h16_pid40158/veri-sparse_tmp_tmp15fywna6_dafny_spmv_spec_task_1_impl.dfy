// ATOM 
function sum(X_val: array<int>, X_crd: array<nat>, v : array<int>, b : int, k : int) : (s : int)
  reads X_val, X_crd, v
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  {
    if k <= b then 
      0
    else  sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b]]
  }

//IMPL SpMV
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
  
  var row := 0;
  while row < y.Length
    /* code modified by LLM (iteration 2): proper loop invariants with bounds checking */
    invariant 0 <= row <= y.Length
    invariant y.Length + 1 == X_pos.Length
    invariant forall i :: 0 <= i < row ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
  {
    var start := X_pos[row];
    var end := X_pos[row + 1];
    
    /* code modified by LLM (iteration 2): compute sum by building from end to start */
    var acc := 0;
    var j := end;
    while j > start
      /* code modified by LLM (iteration 2): modified invariants to match sum definition */
      invariant start <= j <= end
      invariant acc == sum(X_val, X_crd, v, j, end)
      invariant start >= 0
      invariant end <= X_val.Length
    {
      j := j - 1;
      acc := acc + X_val[j] * v[X_crd[j]];
    }
    
    y[row] := acc;
    row := row + 1;
  }
}

//ATOM_PLACEHOLDER_Main