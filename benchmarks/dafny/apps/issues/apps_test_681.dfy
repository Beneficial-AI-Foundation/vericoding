// <vc-preamble>
const MOD := 1000000007

predicate ValidInput(n: int, m: int) {
  1 <= n <= 1000000000000000000 && 2 <= m <= 100
}

function fibonacci_variant(n: int, m: int): int
  requires n >= 0 && m >= 2
  decreases n
{
  if n < m then 1
  else if n == m then 2
  else fibonacci_variant(n-1, m) + fibonacci_variant(n-m, m)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures 0 <= result < MOD
  ensures result == fibonacci_variant(n, m) % MOD
// </vc-spec>
// <vc-code>
{
  if n < m {
    result := 1;
    return;
  }

  var dp := new int[m];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant forall j :: 0 <= j < i ==> dp[j] == 1
  {
    dp[i] := 1;
    i := i + 1;
  }

  var curr := m;
  while curr <= n
    invariant m <= curr <= n + 1
    invariant forall j :: 0 <= j < m ==> 0 <= dp[j] < MOD
    invariant forall k :: 0 <= k < m ==> 
      dp[k] == fibonacci_variant(curr - 1 - ((curr - 1) % m + m - k) % m, m) % MOD
  {
    var next_val := 0;
    var prev_idx := if curr % m == 0 then m - 1 else (curr % m) - 1;
    var m_back_idx := curr % m;
    next_val := (dp[prev_idx] + dp[m_back_idx]) % MOD;

    dp[curr % m] := next_val;
    curr := curr + 1;
  }

  result := dp[n % m];
}
// </vc-code>
