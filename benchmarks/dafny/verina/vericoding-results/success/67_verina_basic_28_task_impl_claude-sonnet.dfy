// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsPrimeHelper(n: nat, k: nat)
  requires k > 0
{
  k >= n || n % k != 0
}

function FindDivisor(n: nat, k: nat): nat
  requires n >= 2 && k >= 2 && k <= n
  decreases n - k
{
  if k >= n then n
  else if n % k == 0 then k
  else FindDivisor(n, k + 1)
}

lemma FindDivisorCorrect(n: nat, k: nat)
  requires n >= 2 && k >= 2 && k <= n
  ensures var d := FindDivisor(n, k); d >= k && d <= n && (d < n ==> n % d == 0)
  decreases n - k
{
  if k >= n {
    // d == n, so d >= k holds
  } else if n % k == 0 {
    // d == k, so d >= k and n % d == 0 hold
  } else {
    FindDivisorCorrect(n, k + 1);
  }
}
// </vc-helpers>

// <vc-spec>
method IsPrime(n: nat) returns (result: bool)
    requires n >= 2
    ensures result ==> forall k: nat :: 2 <= k < n ==> n % k != 0
    ensures !result ==> exists k: nat :: 2 <= k < n && n % k == 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): simplified implementation without helper functions */
  var k := 2;
  while k < n
    invariant 2 <= k <= n
    invariant forall j: nat :: 2 <= j < k ==> n % j != 0
  {
    if n % k == 0 {
      result := false;
      return;
    }
    k := k + 1;
  }
  result := true;
}
// </vc-code>
