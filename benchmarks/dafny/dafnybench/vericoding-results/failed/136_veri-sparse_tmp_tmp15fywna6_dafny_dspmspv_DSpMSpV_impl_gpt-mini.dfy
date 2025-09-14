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
lemma index_seq_at(s: seq<nat>, i: nat)
  requires 0 <= i < |s|
  requires forall u, v :: 0 <= u < v < |s| ==> s[u] < s[v]
  ensures index_seq(s[i], s) == i
{
  if i == 0 {
    // s[0] == s[i], so index_seq(s[i], s) == 0 by definition
  } else {
    // s[0] < s[i], so s[0] != s[i]
    assert s[0] < s[i];
    // By definition of index_seq, since s[0] != s[i]:
    // index_seq(s[i], s) == 1 + index_seq(s[i], s[1..])
    // Apply induction to s[1..] and i-1
    index_seq_at(s[1..], i - 1);
    // After the recursive call, index_seq(s[i], s[1..]) == i-1,
    // hence index_seq(s[i], s) == 1 + (i-1) == i
  }
}

lemma index_array_at(a: array<nat>, i: nat)
  requires a != null
  requires 0 <= i < a.Length
  requires forall u, v :: 0 <= u < v < a.Length ==> a[u] < a[v]
  ensures index(a[i], a) == i
{
  index_seq_at(a[..], i);
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
  var ii := 0;
  while ii < X_len
    invariant 0 <= ii <= X_len
    invariant forall k :: 0 <= k < ii ==> y[k] == 0
  {
    y[ii] := 0;
    ii := ii + 1;
  }

  var j := 0;
  while j < X_crd1.Length
    invariant 0 <= j <= X_crd1.Length
    invariant forall t :: 0 <= t < j ==> y[X_crd1[t]] == sum(X_val, X_crd, v_val, v_crd, X_pos[t], 0, X_pos[t+1], v_val.Length)
    invariant forall i0 :: 0 <= i0 < X_len && (forall t :: 0 <= t < j ==> X_crd1[t] != i0) ==> y[i0] == 0
  {
    var idx := X_crd1[j];
    var start := X_pos[j];
    var end := X_pos[j+1];

    // Help the verifier with bounds and monotonicity facts
    assert 0 <= idx < X_len;
    assert 0 <= start <= X_val.Length;
    assert 0 <= end <= X_val.Length;
    assert start <= end;
    assert start <= X_crd.Length;
    assert end <= X_crd.Length;

    y[idx] := sum(X_val, X_crd, v_val, v_crd, start, 0, end, v_val.Length);
    j := j + 1;
  }
  return y;
}
// </vc-code>

