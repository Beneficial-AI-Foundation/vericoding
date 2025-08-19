//ATOM
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
  
  var i := 0;
  while i < y.Length
    invariant 0 <= i <= y.Length
    invariant forall j :: 0 <= j < i ==> y[j] == sum(X_val, X_crd, v, X_pos[j], X_pos[j + 1])
  {
    y[i] := sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1]);
    i := i + 1;
  }
}

//ATOM
function sum(X_val: array<int>, X_crd: array<nat>, v : array<int>, b : int, k : int) : (s : int)
 reads X_val, X_crd, v
 requires X_val.Length >= b >= 0
 requires k <= X_val.Length
 requires X_val.Length == X_crd.Length
 requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
 {
  if k <= b then 
   0
  else sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b]]
 }

//IMPL
method Main() {
 /* code modified by LLM (iteration 1): Fixed array initialization with proper bounds */
 var X_val := new int[4];
 var X_crd := new nat[4];
 var X_pos := new nat[3];
 var v := new int[4];

 /* code modified by LLM (iteration 1): Initialize arrays to satisfy all preconditions */
 X_val[0] := 1; X_val[1] := 2; X_val[2] := 3; X_val[3] := 4;
 X_crd[0] := 0; X_crd[1] := 1; X_crd[2] := 2; X_crd[3] := 3;
 
 /* code modified by LLM (iteration 1): Set X_pos to be monotonic and within bounds */
 X_pos[0] := 0;
 X_pos[1] := 2;
 X_pos[2] := 4;

 /* code modified by LLM (iteration 1): Initialize v array */
 v[0] := 30;
 v[1] := 31;
 v[2] := 32;
 v[3] := 33;

 var y := SpMV(
  X_val,
  X_crd,
  X_pos,
  v
 );

 /* code modified by LLM (iteration 1): Fixed loop bounds and added proper termination */
 var i := 0;
 while i < y.Length 
   invariant 0 <= i <= y.Length
 { 
   print y[i]; 
   print "; "; 
   i := i + 1; 
 }
}