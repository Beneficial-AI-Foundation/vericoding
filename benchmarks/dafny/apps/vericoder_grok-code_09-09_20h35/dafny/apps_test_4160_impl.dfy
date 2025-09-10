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
method computeDeposit(initial: int, years: int) returns (deposit: int)
    requires initial >= 0
    requires years >= 0
    ensures deposit >= initial
    ensures deposit == calculateDeposit(initial, years)
{
    var dep := initial;
    var y := years;
    while y > 0
        invariant dep >= initial
        invariant calculateDeposit(initial, years - y) == dep
        decreases y
    {
        dep := dep + dep / 100;
        y := y - 1;
    }
    deposit := dep;
}

lemma CalculateDepositIncreasing(a: int, n: int, n2: int)
      requires a >= 0
      requires 0 <= n < n2
      ensures calculateDeposit(a, n) < calculateDeposit(a, n2)
      decreases n2 - n
{
      if n2 == n + 1 {
          var dep := calculateDeposit(a, n);
          assert calculateDeposit(a, n2) == dep + dep / 100;
          if dep > 0 {
              assert dep / 100 > 0;
              assert calculateDeposit(a, n2) > dep;
          } else if a > 0 {
              assert calculateDeposit(a, n) == a > 0;
          } else {
              assert false; // not strict for a=0
          }
      } else {
          CalculateDepositIncreasing(a, n, n2-1);
          CalculateDepositIncreasing(a, n2-1, n2);
          // transitive
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
    var max_years := 12000;
    var low := 0;
    var high := max_years - 1;
    while low <= high
        invariant 0 <= low <= high <= max_years - 1
        invariant calculateDeposit(100, low) < X
        invariant low > 0 ==> calculateDeposit(100, low - 1) < X
        invariant calculateDeposit(100, high + 1) >= X
        decreases high - low + 1
    {
        var mid := low + (high - low) / 2;
        var deposit := computeDeposit(100, mid);
        if deposit >= X {
            high := mid - 1;
        } else {
            low := mid + 1;
        }
    }
    years := low;
}
// </vc-code>

