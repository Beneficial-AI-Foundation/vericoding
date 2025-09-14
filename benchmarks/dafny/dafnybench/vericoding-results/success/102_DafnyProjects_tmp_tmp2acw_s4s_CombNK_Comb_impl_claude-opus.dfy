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
// Helper lemma to establish that comb(i, 0) == 1 for any i
lemma CombZero(i: nat)
  ensures comb(i, 0) == 1
{
  // Follows directly from the definition
}

// Helper lemma to establish that comb(i, i) == 1 for any i
lemma CombDiag(i: nat)
  ensures comb(i, i) == 1
{
  // Follows directly from the definition
}

// Helper lemma for the Pascal's identity recurrence
lemma PascalIdentity(n: nat, k: nat)
  requires 0 < k < n
  ensures comb(n, k) == comb(n-1, k) + comb(n-1, k-1)
{
  // Follows directly from the definition
}
// </vc-helpers>

// <vc-spec>
method Comb(n: nat, k: nat) returns (res: nat)
  requires 0 <= k <= n
  ensures res == comb(n, k)
// </vc-spec>
// <vc-code>
{
  if k == 0 || k == n {
    return 1;
  }
  
  // Create a 2D array to store intermediate results
  var dp := new nat[n+1, n+1];
  
  // Initialize base cases
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall x :: 0 <= x < i ==> dp[x, 0] == 1
    invariant forall x :: 0 <= x < i ==> dp[x, x] == 1
  {
    dp[i, 0] := 1;
    dp[i, i] := 1;
    i := i + 1;
  }
  
  // Fill the dp table using Pascal's identity
  i := 2;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant forall x :: 0 <= x <= n ==> dp[x, 0] == 1
    invariant forall x :: 0 <= x <= n ==> dp[x, x] == 1
    invariant forall x, y :: 2 <= x < i && 0 < y < x ==> 
      dp[x, y] == comb(x, y)
  {
    var j := 1;
    while j < i
      invariant 1 <= j <= i
      invariant forall x :: 0 <= x <= n ==> dp[x, 0] == 1
      invariant forall x :: 0 <= x <= n ==> dp[x, x] == 1
      invariant forall x, y :: 2 <= x < i && 0 < y < x ==> dp[x, y] == comb(x, y)
      invariant forall y :: 1 <= y < j ==> dp[i, y] == comb(i, y)
    {
      dp[i, j] := dp[i-1, j] + dp[i-1, j-1];
      assert dp[i-1, j] == comb(i-1, j) by {
        if j == i-1 {
          assert dp[i-1, j] == dp[i-1, i-1] == 1 == comb(i-1, i-1);
        } else {
          assert 2 <= i-1 < i && 0 < j < i-1;
        }
      }
      assert dp[i-1, j-1] == comb(i-1, j-1) by {
        if j-1 == 0 {
          assert dp[i-1, 0] == 1 == comb(i-1, 0);
        } else {
          assert 2 <= i-1 < i && 0 < j-1 < i-1;
        }
      }
      PascalIdentity(i, j);
      assert dp[i, j] == comb(i, j);
      j := j + 1;
    }
    i := i + 1;
  }
  
  assert dp[n, k] == comb(n, k) by {
    if k == 1 || k == n-1 {
      if k == 1 {
        assert 2 <= n < n+1 && 0 < 1 < n;
      } else {
        assert 2 <= n < n+1 && 0 < n-1 < n;
      }
    } else {
      assert 2 <= n < n+1 && 0 < k < n;
    }
  }
  
  res := dp[n, k];
}
// </vc-code>

