/* 
* Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial recursive definition of C(n, k), based on the Pascal equality.
function comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{
  if k == 0 || k == n then 1 else comb(n-1, k) + comb(n-1, k-1)  
}

// <vc-helpers>
lemma CombRecurrence(n: nat, k: nat)
  requires 0 < k < n
  ensures comb(n, k) == comb(n-1, k) + comb(n-1, k-1)
{
  // comb is defined by the Pascal equality in its body,
  // and the precondition rules out the base cases k==0 or k==n,
  // so the function body unfolds to the desired equality.
  assert comb(n, k) == (comb(n-1, k) + comb(n-1, k-1));
}

lemma CombEdge0(n: nat)
  ensures comb(n, 0) == 1
{
  assert comb(n, 0) == 1;
}

lemma CombEdgeDiag(n: nat)
  ensures comb(n, n) == 1
{
  assert comb(n, n) == 1;
}
// </vc-helpers>

// <vc-spec>
method Comb(n: nat, k: nat) returns (res: nat)
  requires 0 <= k <= n
  ensures res == comb(n, k)
// </vc-spec>
// <vc-code>
{
  var C := new nat[k + 1];
  var t := 0;
  while t <= k
    invariant 0 <= t <= k + 1
    invariant forall q | 0 <= q < t ::
      if q == 0 then C[q] == comb(0, q) else C[q] == 0
    decreases k - t + 1
  {
    if t == 0 {
      C[0] := 1;
      CombEdge0(0);
    } else {
      C[t] := 0;
    }
    t := t + 1;
  }
  assert forall t0 | 0 <= t0 <= k :: if t0 <= 0 then C[t0] == comb(0, t0) else C[t0] == 0;
  var i := 1;
  // Invariant: C[t] == comb(i-1, t) for t <= i-1, else 0, and 1 <= i <= n+1
  while i <= n
    invariant 1 <= i <= n + 1
    invariant forall t | 0 <= t <= k ::
      if t <= i-1 then C[t] == comb(i-1, t) else C[t] == 0
    decreases n - i + 1
  {
    var m := if i < k then i else k; // min(i,k)
    var j := m;
    // Inner loop: we are transforming row i-1 into row i,
    // updating positions from m down to 1.
    while j >= 1
      invariant 0 <= j <= m
      invariant forall t | 0 <= t <= k ::
        if t > j && t <= m then C[t] == comb(i, t)
        else if t <= j then if t <= i-1 then C[t] == comb(i-1, t) else C[t] == 0
        else C[t] == 0
      decreases j
    {
      if j == i {
        // j == i: by the invariant C[j] == 0 and C[j-1] == comb(i-1, j-1)
        assert C[j] == 0;
        assert C[j-1] == comb(i-1, j-1);
        // comb(i,i) == 1 and C[j] will become 1 after the update
        CombEdgeDiag(i);
        C[j] := C[j] + C[j-1];
      } else {
        // 0 < j < i: use Pascal recurrence
        assert 0 < j < i;
        assert C[j] == comb(i-1, j);
        assert C[j-1] == comb(i-1, j-1);
        CombRecurrence(i, j);
        C[j] := C[j] + C[j-1];
      }
      j := j - 1;
    }
    // after inner loop, C[t] == comb(i, t) for all t <= m.
    i := i + 1;
  }
  // At loop exit i == n+1, so C[t] == comb(n, t) for all t <= k
  res := C[k];
}
// </vc-code>

