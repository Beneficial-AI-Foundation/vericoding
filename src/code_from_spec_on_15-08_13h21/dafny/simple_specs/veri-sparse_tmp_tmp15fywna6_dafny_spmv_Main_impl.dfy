method SpMV(X_val: array<int>, X_crd: array<nat>, X_pos: array<nat>, v : array<int>) returns (y : array<int>)
 requires X_crd.Length >= 1 
 requires X_crd.Length == X_val.Length
 requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j]
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
    invariant y.Length + 1 == X_pos.Length
    invariant forall i :: 0 <= i < row ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
  {
    y[row] := sum(X_val, X_crd, v, X_pos[row], X_pos[row + 1]);
    row := row + 1;
  }
}

//ATOM
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
  else sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b]]
 }

//IMPL
method Main() {
 var X_val := new int[4](i => 1);
 /* code modified by LLM (iteration 1): Fixed X_crd initialization to ensure all values are less than v.Length (8) */
 var X_crd := new nat[4](i => if i <= 3 then (3 - i) else 0);
 var X_pos := new nat[9];
 X_pos[0] := 0;
 X_pos[1] := 1;
 X_pos[2] := 1;
 X_pos[3] := 2;
 X_pos[4] := 2;
 X_pos[5] := 3;
 X_pos[6] := 3;
 X_pos[7] := 4;
 X_pos[8] := 4;

 var v := new int[8];

 v[0] := 30;
 v[1] := 0;
 v[2] := 31;
 v[3] := 0;
 v[4] := 32;
 v[5] := 0;
 v[6] := 33;
 v[7] := 0;

 var y := SpMV(X_val, X_crd, X_pos, v);

 /* code modified by LLM (iteration 1): Fixed loop bound to match actual array length */
 var i := 0;
 while i < y.Length { print y[i]; print "; "; i := i + 1; }
}