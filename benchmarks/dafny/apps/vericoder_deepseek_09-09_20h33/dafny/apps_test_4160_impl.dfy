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
    var prev := calculateDeposit(initial, n - 1);
    assert calculateDeposit(initial, n) == prev + prev / 100;
    assert prev <= calculateDeposit(initial, n);
  }
}

lemma calculateDepositGeometricGrowth(initial: int, years: nat)
  requires initial >= 0
  ensures calculateDeposit(initial, years) >= initial * (101/100)^years
  decreases years
{
  if years > 0 {
    calculateDepositGeometricGrowth(initial, years - 1);
    var prev := calculateDeposit(initial, years - 1);
    assert calculateDeposit(initial, years) == prev + prev / 100;
    assert calculateDeposit(initial, years) >= prev * 101/100;
    assert prev * 101/100 >= initial * (101/100)^(years - 1) * 101/100;
    assert initial * (101/100)^(years - 1) * 101/100 == initial * (101/100)^years;
  }
}

lemma calculateDepositEventuallyLargeEnough(initial: int, X: int, k: nat)
  requires initial >= 0
  requires X > initial
  ensures exists n: nat :: n <= k && calculateDeposit(initial, n) >= X
  decreases k
{
  if k == 0 {
    // Base case: n = 0 would have calculateDeposit(initial, 0) = initial < X
  } else {
    calculateDepositEventuallyLargeEnough(initial, X, k - 1);
    if calculateDeposit(initial, k - 1) < X {
      calculateDepositGeometricGrowth(initial, k);
      assert calculateDeposit(initial, k) >= initial * (101/100)^k;
      // For large enough k, this will eventually exceed X
    }
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
  var deposit := 100;
  years := 0;
  
  while deposit < X
    invariant years >= 0
    invariant deposit == calculateDeposit(100, years)
    invariant deposit < X
    decreases X - deposit
  {
    years := years + 1;
    deposit := deposit + deposit / 100;
  }
}
// </vc-code>

