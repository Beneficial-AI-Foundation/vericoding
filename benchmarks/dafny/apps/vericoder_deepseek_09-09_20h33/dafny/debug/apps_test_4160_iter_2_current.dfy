function calculateDeposit(initial: int, years: int): int
    requires initial >= 0
    requires years >= 0
{
    if years == 0 then initial
    else 
        var prevDeposit := calculateDeposit(initial, years - 1);
        prevDeposit + prevDeposit / 100
}

// <vc-helpers>
lemma calculateDepositIncreases(initial: int, m: nat, n: nat)
  requires initial >= 0
  requires m <= n
  ensures calculateDeposit(initial, m) <= calculateDeposit(initial, n)
  decreases n - m
{
  if m < n {
    calculateDepositIncreases(initial, m, n - 1);
    assert calculateDeposit(initial, n - 1) <= calculateDeposit(initial, n);
  }
}

lemma calculateDepositExact(initial: int, years: nat)
  requires initial >= 0
  ensures calculateDeposit(initial, years) == initial + initial * years / 100
  decreases years
{
  if years > 0 {
    calculateDepositExact(initial, years - 1);
    var prev := calculateDeposit(initial, years - 1);
    assert prev == initial + initial * (years - 1) / 100;
    assert calculateDeposit(initial, years) == prev + prev / 100;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(X: int) returns (years: int)
    requires X >= 101
    ensures years >= 0
    ensures var finalDeposit := calculateDeposit(100, years); finalDeposit >= X
    ensures years == 0 || calculateDeposit(100, years - 1) < X
// </vc-spec>
// <vc-code>
{
  years := 0;
  while calculateDeposit(100, years) < X
    invariant years >= 0
    invariant calculateDeposit(100, years) < X
    decreases X - calculateDeposit(100, years)
  {
    years := years + 1;
  }
}
// </vc-code>

