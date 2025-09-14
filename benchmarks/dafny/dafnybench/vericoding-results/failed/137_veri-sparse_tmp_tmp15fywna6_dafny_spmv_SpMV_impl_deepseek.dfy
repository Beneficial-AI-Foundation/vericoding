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
lemma sum_empty(X_val: array<int>, X_crd: array<nat>, v: array<int>, b: int, k: int)
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  requires k <= b
  ensures sum(X_val, X_crd, v, b, k) == 0
{
}

lemma sum_split(X_val: array<int>, X_crd: array<nat>, v: array<int>, b: int, m: int, k: int)
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  requires b <= m <= k
  ensures sum(X_val, X_crd, v, b, k) == sum(X_val, X_crd, v, b, m) + sum(X_val, X_crd, v, m, k)
  decreases k - b
{
  if k <= b {
  } else if m == b {
  } else if m == k {
  } else {
    calc {
      sum(X_val, X_crd, v, b, k);
      == { if b < k { sum_step(X_val, X_crd, v, b, k); } }
      X_val[b] * v[X_crd[b]] + sum(X_val, X_crd, v, b + 1, k);
      == { sum_split(X_val, X_crd, v, b + 1, m, k); }
      X_val[b] * v[X_crd[b]] + (sum(X_val, X_crd, v, b + 1, m) + sum(X_val, X_crd, v, m, k));
      == { if b + 1 <= m { sum_split(X_val, X_crd, v, b, b + 1, m); } }
      (X_val[b] * v[X_crd[b]] + sum(X_val, X_crd, v, b + 1, m)) + sum(X_val, X_crd, v, m, k);
      == { if b < m { sum_step(X_val, X_crd, v, b, m); } }
      sum(X_val, X_crd, v, b, m) + sum(X_val, X_crd, v, m, k);
    }
  }
}

lemma sum_step(X_val: array<int>, X_crd: array<nat>, v: array<int>, b: int, k: int)
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  requires b < k
  ensures sum(X_val, X_crd, v, b, k) == X_val[b] * v[X_crd[b]] + sum(X_val, X_crd, v, b + 1, k)
  decreases k - b
{
  if b + 1 < k {
    sum_step(X_val, X_crd, v, b + 1, k);
  }
}

lemma sum_append_single(X_val: array<int>, X_crd: array<nat>, v: array<int>, b: int, k: int)
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  requires b < k
  ensures sum(X_val, X_crd, v, b, k) == sum(X_val, X_crd, v, b, k - 1) + X_val[k - 1] * v[X_crd[k - 1]]
{
  sum_split(X_val, X_crd, v, b, k - 1, k);
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
  var row := 0;
  while row < y.Length
    invariant 0 <= row <= y.Length
    invariant forall i :: 0 <= i < row ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
  {
    y[row] := 0;
    var j := X_pos[row];
    if j < X_pos[row + 1] {
      while j < X_pos[row + 1]
        invariant X_pos[row] <= j <= X_pos[row + 1]
        invariant y[row] == sum(X_val, X_crd, v, X_pos[row], j)
        decreases X_pos[row + 1] - j
      {
        y[row] := y[row] + X_val[j] * v[X_crd[j]];
        j := j + 1;
        if j <= X_pos[row + 1] {
          calc {
            y[row];
            ==
            sum(X_val, X_crd, v, X_pos[row], j - 1) + X_val[j - 1] * v[X_crd[j - 1]];
            == { sum_append_single(X_val, X_crd, v, X_pos[row], j); }
            sum(X_val, X_crd, v, X_pos[row], j);
          }
        }
      }
    } else {
      sum_empty(X_val, X_crd, v, X_pos[row], X_pos[row + 1]);
    }
    row := row + 1;
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