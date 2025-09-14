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

  decreases pX_end + pV_end - (kX + kV)
  {
    if pV_end <= kV || pX_end <= kX then 
      0
    else if X_crd[kX] == v_crd[kV] then 
      sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + v_val[kV] * X_val[kX]
    else if X_crd[kX] < v_crd[kV] then 
      sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    else sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
  }

function min(x : nat, y : nat) : nat {
  if x <= y then x else y
}

predicate notin(y: nat, x : array<nat>) 
  reads x
{
  forall i :: 0 <= i < x.Length ==> y != x[i]
}

predicate notin_seq(y: nat, x : seq<nat>) 
{
  forall i :: 0 <= i < |x| ==> y != x[i]
}

function index_seq(x : nat, y: seq<nat>) : (i : nat)
  ensures i >= |y| ==> notin_seq(x, y)
  ensures i <  |y| ==> y[i] == x
{
  if |y| == 0 then 0 
  else 
    if y[0] == x then 0 
    else 1 + index_seq(x, y[1..])
}

function index(x : nat, y: array<nat>) : (i : nat)
  reads y
  ensures i >= y.Length ==> notin(x, y)
  ensures i <  y.Length ==> y[i] == x
{
  index_seq(x, y[.. ])
}

// <vc-helpers>
lemma IndexBounds(i: nat, X_crd1: array<nat>)
  ensures index(i, X_crd1) <= X_crd1.Length
{
  var idx := index_seq(i, X_crd1[..]);
  IndexSeqBounds(i, X_crd1[..]);
  assert idx <= |X_crd1[..]|;
  assert |X_crd1[..]| == X_crd1.Length;
}

lemma IndexSeqBounds(x: nat, y: seq<nat>)
  ensures index_seq(x, y) <= |y|
{
  if |y| == 0 {
    assert index_seq(x, y) == 0;
  } else if y[0] == x {
    assert index_seq(x, y) == 0;
  } else {
    IndexSeqBounds(x, y[1..]);
    assert index_seq(x, y) == 1 + index_seq(x, y[1..]);
    assert index_seq(x, y[1..]) <= |y[1..]|;
    assert |y[1..]| == |y| - 1;
  }
}

lemma SumShift(X_val: array<int>, X_crd: array<nat>, v_val: array<int>, v_crd: array<nat>,
               kX: nat, kV: nat, row_start: nat, row_end: nat)
  requires X_val.Length == X_crd.Length
  requires v_val.Length == v_crd.Length
  requires row_start <= kX <= row_end <= X_crd.Length
  requires 0 <= kV <= v_crd.Length
  ensures sum(X_val, X_crd, v_val, v_crd, row_start, 0, kX, kV) + 
          sum(X_val, X_crd, v_val, v_crd, kX, kV, row_end, v_val.Length) ==
          sum(X_val, X_crd, v_val, v_crd, row_start, 0, row_end, v_val.Length)
  decreases row_end - kX + v_val.Length - kV
{
  if kX >= row_end || kV >= v_val.Length {
    // Base case: no more elements to process
  } else if X_crd[kX] == v_crd[kV] {
    SumShift(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, row_start, row_end);
  } else if X_crd[kX] < v_crd[kV] {
    SumShift(X_val, X_crd, v_val, v_crd, kX + 1, kV, row_start, row_end);
  } else {
    SumShift(X_val, X_crd, v_val, v_crd, kX, kV + 1, row_start, row_end);
  }
}
// </vc-helpers>

// <vc-spec>
method DSpMSpV(X_val : array<int>, X_crd : array<nat>, X_pos : array<nat>,
                                  X_crd1 : array<nat>, X_len: nat,
              v_val : array<int>, v_crd : array<nat>) returns (y : array<int>)
  // X requirements 
  requires X_pos.Length >= 1
  requires X_val.Length == X_crd.Length
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j];
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
// </vc-spec>
// <vc-code>
{
  y := new int[X_len];
  var i := 0;
  
  while i < X_len
    invariant 0 <= i <= X_len
    invariant y.Length == X_len
    invariant forall j :: 0 <= j < i ==> 
      y[j] == 
        if index(j, X_crd1) < X_crd1.Length then 
          sum(X_val, X_crd, v_val, v_crd, X_pos[index(j, X_crd1)], 0, X_pos[index(j, X_crd1)+1], v_val.Length)
        else 0
  {
    IndexBounds(i, X_crd1);
    var idx := index(i, X_crd1);
    
    if idx < X_crd1.Length {
      // i is a non-zero row index
      var row_start := X_pos[idx];
      var row_end := X_pos[idx + 1];
      
      // Compute the dot product for this row
      var s := 0;
      var kX := row_start;
      var kV := 0;
      
      while kX < row_end && kV < v_val.Length
        invariant row_start <= kX <= row_end
        invariant 0 <= kV <= v_val.Length
        invariant s == sum(X_val, X_crd, v_val, v_crd, row_start, 0, kX, kV)
        invariant sum(X_val, X_crd, v_val, v_crd, row_start, 0, kX, kV) + 
                  sum(X_val, X_crd, v_val, v_crd, kX, kV, row_end, v_val.Length) ==
                  sum(X_val, X_crd, v_val, v_crd, row_start, 0, row_end, v_val.Length)
      {
        SumShift(X_val, X_crd, v_val, v_crd, kX, kV, row_start, row_end);
        
        if X_crd[kX] == v_crd[kV] {
          s := s + X_val[kX] * v_val[kV];
          kX := kX + 1;
          kV := kV + 1;
        } else if X_crd[kX] < v_crd[kV] {
          kX := kX + 1;
        } else {
          kV := kV + 1;
        }
      }
      
      assert kX == row_end || kV == v_val.Length;
      assert s == sum(X_val, X_crd, v_val, v_crd, row_start, 0, kX, kV);
      SumShift(X_val, X_crd, v_val, v_crd, kX, kV, row_start, row_end);
      assert s + sum(X_val, X_crd, v_val, v_crd, kX, kV, row_end, v_val.Length) == 
             sum(X_val, X_crd, v_val, v_crd, row_start, 0, row_end, v_val.Length);
      assert sum(X_val, X_crd, v_val, v_crd, kX, kV, row_end, v_val.Length) == 0;
      assert s == sum(X_val, X_crd, v_val, v_crd, row_start, 0, row_end, v_val.Length);
      y[i] := s;
    } else {
      // i is not a non-zero row index
      y[i] := 0;
    }
    
    i := i + 1;
  }
}
// </vc-code>

