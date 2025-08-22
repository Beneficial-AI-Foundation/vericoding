//ATOM

predicate notin(y: nat, x : array<nat>) 
 reads x
{
 forall i :: 0 <= i < x.Length ==> y != x[i]
}


//ATOM

method DSpMSpV(X_val : array<int>, X_crd : array<nat>, X_pos : array<nat>,
                 X_crd1 : array<nat>, X_len: nat,
       v_val : array<int>, v_crd : array<nat>) returns (y : array<int>)
 // X requirements 
 requires X_pos.Length >= 1
 requires X_val.Length == X_crd.Length
 requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j]
 requires forall i :: 0 <= i < X_pos.Length ==> 0 <= X_pos[i] <= X_val.Length

 requires X_len >= X_crd1.Length
 requires forall i :: 0 <= i < X_crd1.Length ==> X_crd1[i] < X_len

 requires X_crd1.Length < X_pos.Length
 requires forall i, j :: 0 <= i < j < X_crd1.Length ==> X_crd1[i] < X_crd1[j]

 // v requirements 
 requires v_val.Length == v_crd.Length

 ensures y.Length == X_len
 ensures forall i :: 0 <= i < y.Length ==> 
  y[i] == 
   if index(i, X_crd1) < X_crd1.Length then 
    sum(X_val, X_crd, v_val, v_crd, X_pos[index(i, X_crd1)], 0, X_pos[index(i, X_crd1)+1], v_val.Length)
   else 0
 {
  /* code modified by LLM (iteration 1): Fixed array initialization and bounds checking */
  y := new int[X_len];
  
  var idx := 0;
  while idx < X_len
    invariant 0 <= idx <= X_len
    invariant y.Length == X_len
    invariant forall i :: 0 <= i < idx ==> 
      y[i] == 
        if index(i, X_crd1) < X_crd1.Length then 
          sum(X_val, X_crd, v_val, v_crd, X_pos[index(i, X_crd1)], 0, X_pos[index(i, X_crd1)+1], v_val.Length)
        else 0
  {
    var pos_idx := index(idx, X_crd1);
    if pos_idx < X_crd1.Length {
      /* code modified by LLM (iteration 1): Added proper bounds check for X_pos array access */
      assert pos_idx < X_crd1.Length;
      assert X_crd1.Length < X_pos.Length;
      assert pos_idx + 1 < X_pos.Length;
      y[idx] := sum(X_val, X_crd, v_val, v_crd, X_pos[pos_idx], 0, X_pos[pos_idx+1], v_val.Length);
    } else {
      y[idx] := 0;
    }
    idx := idx + 1;
  }
}


//ATOM
function sum(X_val : array<int>, X_crd : array<nat>,
       v_val : array<int>, v_crd : array<nat>, kX : nat, kV : nat, pX_end : nat, pV_end : nat) : (s : int) 
 reads X_val, X_crd
 requires X_val.Length == X_crd.Length
 requires pX_end <= X_crd.Length
 requires 0 <= kX <= X_crd.Length

 reads v_crd, v_val
 requires v_val.Length == v_crd.Length
 requires pV_end <= v_crd.Length
 requires 0 <= kV <= v_crd.Length

 {
  if pV_end <= kV || pX_end <= kX then 
   0
  else if X_crd[kX] == v_crd[kV] then 
   sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + v_val[kV] * X_val[kX]
  else if X_crd[kX] < v_crd[kV] then 
   sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
  else sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
 }


//ATOM

function index_seq(x : nat, y: seq<nat>) : (i : nat)
 ensures i >= |y| ==> notin_seq(x, y)
 ensures i < |y| ==> y[i] == x
{
 if |y| == 0 then 0 
 else 
  if y[0] == x then 0 
  else 1 + index_seq(x, y[1..])
}


//ATOM

function min(x : nat, y : nat) : nat {
 if x <= y then x else y
}


//ATOM

predicate notin_seq(y: nat, x : seq<nat>) 
{
 forall i :: 0 <= i < |x| ==> y != x[i]
}


//ATOM

function index(x : nat, y: array<nat>) : (i : nat)
 reads y
 ensures i >= y.Length ==> notin(x, y)
 ensures i < y.Length ==> y[i] == x
{
 index_seq(x, y[.. ])
}


//IMPL Main

method Main() {
 /* code modified by LLM (iteration 1): Fixed array initialization and added proper precondition validation */
 var X_val := new int[4];
 X_val[0] := 1; X_val[1] := 1; X_val[2] := 1; X_val[3] := 1;
 
 var X_crd := new nat[4];
 X_crd[0] := 6; X_crd[1] := 4; X_crd[2] := 2; X_crd[3] := 0;
 
 var X_pos := new nat[5];
 X_pos[0] := 0; X_pos[1] := 1; X_pos[2] := 2; X_pos[3] := 3; X_pos[4] := 4;
 
 var X_crd1 := new nat[4];
 X_crd1[0] := 0; X_crd1[1] := 2; X_crd1[2] := 4; X_crd1[3] := 6;
 
 var X_len := 8;

 var v_val := new int[4];
 v_val[0] := 30; v_val[1] := 31; v_val[2] := 32; v_val[3] := 33;
 
 var v_crd := new nat[4];
 v_crd[0] := 0; v_crd[1] := 2; v_crd[2] := 4; v_crd[3] := 6;

 var y := DSpMSpV(
  X_val,
  X_crd,
  X_pos,
  X_crd1,
  X_len,
  v_val,
  v_crd
 );

 var i := 0;
 while i < 8 
   invariant 0 <= i <= 8
 { 
  print y[i]; 
  print "; "; 
  i := i + 1; 
 }
}