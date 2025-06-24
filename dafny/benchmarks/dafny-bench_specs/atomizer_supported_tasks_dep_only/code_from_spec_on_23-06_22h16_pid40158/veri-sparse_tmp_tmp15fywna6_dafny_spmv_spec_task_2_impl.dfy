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

/* code modified by LLM (iteration 1): added helper lemma to prove sum properties */
lemma SumProperty(X_val: array<int>, X_crd: array<nat>, v : array<int>, b : int, k : int)
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  requires b < k
  ensures sum(X_val, X_crd, v, b, k) == sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b]]
{
  // Follows directly from the definition of sum
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
      invariant 0 <= row <= y.Length
      invariant forall i :: 0 <= i < row ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
    {
      var start := X_pos[row];
      var end := X_pos[row + 1];
      
      var result := 0;
      var j := start;
      
      while j < end
        invariant start <= j <= end
        invariant result == sum(X_val, X_crd, v, start, j)
        /* code modified by LLM (iteration 1): simplified invariants focusing on essential properties */
        invariant 0 <= start <= X_val.Length
        invariant 0 <= end <= X_val.Length
      {
        /* code modified by LLM (iteration 1): use helper lemma to prove sum property */
        if j + 1 <= end {
          SumProperty(X_val, X_crd, v, j, j + 1);
        }
        
        result := result + X_val[j] * v[X_crd[j]];
        j := j + 1;
      }
      
      y[row] := result;
      row := row + 1;
    }
  }

method Main() {
}