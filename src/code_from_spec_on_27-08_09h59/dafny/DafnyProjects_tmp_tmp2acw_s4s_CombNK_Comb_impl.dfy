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
function min(a: int, b: int): int
{
  if a <= b then a else b
}

lemma CombSymmetry(n: nat, k: nat)
  requires 0 <= k <= n
  ensures comb(n, k) == comb(n, n - k)
{
  if k == 0 || k == n {
    assert comb(n, k) == 1;
    assert comb(n, n - k) == 1;
  } else if k == 1 {
    CombBaseCase(n);
  } else {
    CombSymmetry(n - 1, k);
    CombSymmetry(n - 1, k - 1);
  }
}

lemma CombBaseCase(n: nat)
  requires n >= 1
  ensures comb(n, 1) == n
  ensures comb(n, n - 1) == n
{
  if n == 1 {
    assert comb(1, 1) == 1;
    assert comb(1, 0) == 1;
  } else {
    CombBaseCase(n - 1);
    assert comb(n, 1) == comb(n-1, 1) + comb(n-1, 0);
    assert comb(n-1, 0) == 1;
    assert comb(n, 1) == (n-1) + 1;
    assert comb(n, 1) == n;
  }
}

lemma CombMonotonic(n: nat, k: nat)
  requires 0 <= k <= n
  ensures comb(n, k) >= 1
{
  if k == 0 || k == n {
    assert comb(n, k) == 1;
  } else if k >= n {
    assert false;
  } else {
    CombMonotonic(n - 1, k);
    CombMonotonic(n - 1, k - 1);
  }
}

lemma CombRecursive(n: nat, k: nat)
  requires 1 <= k < n
  ensures comb(n, k) == comb(n-1, k) + comb(n-1, k-1)
{
  assert comb(n, k) == comb(n-1, k) + comb(n-1, k-1);
}

lemma TableInvariantHelper(i: nat, j: nat, k: nat)
  requires 1 <= j < i
  requires 1 <= i
  requires 1 <= k
  requires j <= k
  ensures j <= min(i-1, k)
  ensures j-1 <= min(i-1, k)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Comb(n: nat, k: nat) returns (res: nat)
  requires 0 <= k <= n
  ensures res == comb(n, k)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if k == 0 || k == n {
    return 1;
  }
  
  var table := new nat[n + 1, k + 1];
  
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall row :: 0 <= row < i ==> table[row, 0] == 1
  {
    table[i, 0] := 1;
    i := i + 1;
  }
  
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant forall row :: 0 <= row < n + 1 ==> table[row, 0] == 1
    invariant forall row :: 1 <= row < i && 1 <= k ==> 
      forall col :: 1 <= col <= min(row, k) ==> 
        table[row, col] == comb(row, col)
  {
    var j := 1;
    while j <= min(i, k)
      invariant 1 <= j <= min(i, k) + 1
      invariant forall row :: 0 <= row < n + 1 ==> table[row, 0] == 1
      invariant forall row :: 1 <= row < i && 1 <= k ==> 
        forall col :: 1 <= col <= min(row, k) ==> 
          table[row, col] == comb(row, col)
      invariant forall col :: 1 <= col < j ==> table[i, col] == comb(i, col)
    {
      if j == i {
        table[i, j] := 1;
        assert comb(i, i) == 1;
      } else {
        assert j < i;
        assert 1 <= j <= k;
        assert i >= 2;
        TableInvariantHelper(i, j, k);
        assert j <= min(i-1, k);
        assert j-1 <= min(i-1, k);
        assert j-1 >= 0;
        assert table[i-1, j] == comb(i-1, j);
        assert table[i-1, j-1] == comb(i-1, j-1);
        CombRecursive(i, j);
        table[i, j] := table[i - 1, j] + table[i - 1, j - 1];
        assert table[i, j] == comb(i, j);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  assert n < n + 1;
  assert 1 <= k;
  assert k <= min(n, k);
  assert table[n, k] == comb(n, k);
  return table[n, k];
}
// </vc-code>
