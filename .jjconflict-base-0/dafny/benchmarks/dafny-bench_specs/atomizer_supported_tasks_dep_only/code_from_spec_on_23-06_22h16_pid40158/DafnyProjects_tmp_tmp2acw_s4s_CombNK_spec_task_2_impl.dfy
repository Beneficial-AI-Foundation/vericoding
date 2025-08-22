/* 
* Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial recursive definition of C(n, k), based on the Pascal equality.
//ATOM comb
function comb(n: nat, k: nat): nat
  requires k <= n
{
  if k == 0 || k == n then 1
  else comb(n-1, k-1) + comb(n-1, k)
}

// Calculates C(n,k) iteratively in time O(k*(n-k)) and space O(n-k), 
// with dynamic programming.
method combIterative(n: nat, k: nat) returns (result: nat)
  requires k <= n
  ensures result == comb(n, k)
{
  if k == 0 || k == n {
    return 1;
  }
  
  /* code modified by LLM (iteration 1): Optimized approach using 1D array with proper verification */
  var actualK := if k > n - k then n - k else k;
  
  // Use single array that gets updated in place
  var dp := new nat[actualK + 1];
  
  // Initialize: C(0, 0) = 1, C(0, j) = 0 for j > 0
  dp[0] := 1;
  var j := 1;
  while j <= actualK
    invariant 1 <= j <= actualK + 1
    invariant dp.Length == actualK + 1
    invariant dp[0] == 1
    invariant forall jj | 1 <= jj < j :: dp[jj] == 0
  {
    dp[jj] := 0;
    j := j + 1;
  }
  
  /* code modified by LLM (iteration 1): Main DP computation with proper invariants */
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant dp.Length == actualK + 1
    invariant forall jj | 0 <= jj <= actualK :: dp[jj] == comb(i-1, jj)
  {
    // Update dp array from right to left to avoid overwriting needed values
    var jj := if actualK <= i-1 then actualK else i-1;
    while jj >= 1
      invariant 0 <= jj <= actualK
      invariant jj <= i-1 + 1
      invariant dp[0] == comb(i-1, 0) == 1
      invariant forall j_idx | jj < j_idx <= actualK && j_idx <= i-1 :: dp[j_idx] == comb(i, j_idx)
      invariant forall j_idx | 0 <= j_idx <= actualK && j_idx > i-1 :: dp[j_idx] == 0
      invariant forall j_idx | jj <= j_idx <= actualK && j_idx <= i-1 :: dp[j_idx] == comb(i-1, j_idx)
    {
      /* code modified by LLM (iteration 1): Apply Pascal's recurrence relation */
      if jj <= i-1 {
        var old_val := dp[jj];
        dp[jj] := dp[jj-1] + dp[jj];
        
        // Verify Pascal's identity
        assert dp[jj-1] == comb(i-1, jj-1);
        assert old_val == comb(i-1, jj);
        assert comb(i-1, jj-1) + comb(i-1, jj) == comb(i, jj) by {
          // This follows from the recursive definition of comb
          if jj == i {
            assert comb(i, jj) == comb(i, i) == 1;
            assert comb(i-1, jj-1) == comb(i-1, i-1) == 1;
            assert comb(i-1, jj) == comb(i-1, i) == 0; // This is impossible since jj <= i-1
          }
        }
      }
      jj := jj - 1;
    }
    
    // Update dp[0] which is always 1
    dp[0] := 1;
    
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Use symmetry property correctly */
  result := dp[actualK];
  
  if k > n - k {
    // We computed comb(n, n-k) but need comb(n, k)
    // By symmetry: comb(n, k) == comb(n, n-k)
    combSymmetry(n, k);
    assert result == comb(n, actualK);
    assert actualK == n - k;
    assert comb(n, n-k) == comb(n, k);
    assert result == comb(n, k);
  } else {
    assert actualK == k;
    assert result == comb(n, k);
  }
}

//ATOM combProps
lemma combSymmetry(n: nat, k: nat)
  requires k <= n
  ensures comb(n, k) == comb(n, n - k)
{
  if k == 0 || k == n {
    // Base cases
  } else if k == n - k {
    // Already equal
  } else if k < n - k {
    combSymmetry(n - 1, k - 1);
    combSymmetry(n - 1, k);
    combSymmetry(n - 1, n - k - 1);
    combSymmetry(n - 1, n - k);
  } else {
    combSymmetry(n - 1, k - 1);
    combSymmetry(n - 1, k);
    combSymmetry(n - 1, n - k - 1);
    combSymmetry(n - 1, n - k);
  }
}

//ATOM Main
method Main() {
  var result := combIterative(5, 2);
  print "C(5,2) = ", result, "\n";
  
  result := combIterative(10, 3);
  print "C(10,3) = ", result, "\n";
}

//IMPL testComb
method testComb() {
  /* code modified by LLM (iteration 1): Simple test cases with explicit assertions */
  var result1 := combIterative(5, 2);
  // C(5,2) = C(4,1) + C(4,2) = 4 + 6 = 10
  assert result1 == comb(5, 2);
  
  var result2 := combIterative(4, 0);
  assert result2 == comb(4, 0);
  assert result2 == 1;
  
  var result3 := combIterative(6, 6);
  assert result3 == comb(6, 6);
  assert result3 == 1;
  
  var result4 := combIterative(4, 2);
  // C(4,2) = C(3,1) + C(3,2) = 3 + 3 = 6
  assert result4 == comb(4, 2);
}