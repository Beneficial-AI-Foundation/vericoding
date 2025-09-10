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
lemma deposit_ge_100_plus_n(n: int)
  requires n >= 0
  ensures calculateDeposit(100, n) >= 100 + n
  decreases n
{
  if n == 0 {
    // calculateDeposit(100,0) == 100
  } else {
    deposit_ge_100_plus_n(n - 1);
    var prev := calculateDeposit(100, n - 1);
    assert prev >= 100 + (n - 1);
    assert prev >= 100;
    assert prev / 100 >= 1;
    assert calculateDeposit(100, n) == prev + prev / 100;
    assert calculateDeposit(100, n) >= prev + 1;
    assert prev + 1 >= 100 + (n - 1) + 1;
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
  var y := 0;
  var dep := calculateDeposit(100, 0);
  // X >= 101 implies X - 100 >= 1, so X - 100 is non-negative
  while dep < X && y < X - 100
    invariant 0 <= y <= X - 100
    invariant dep == calculateDeposit(100, y)
    invariant y == 0 || calculateDeposit(100, y - 1) < X
    decreases X - 100 - y
  {
    // before increment, dep < X (loop guard), so after increment
    // we maintain that calculateDeposit(100, y-1) < X
    y := y + 1;
    dep := calculateDeposit(100, y);
  }
  // After loop, either dep >= X or y == X - 100.
  // In the latter case deposit_ge_100_plus_n ensures dep >= X.
  if dep < X {
    // then must have y == X - 100
    deposit_ge_100_plus_n(y);
    // now dep == calculateDeposit(100,y) >= 100 + y == X
    dep := calculateDeposit(100, y);
  }
  years := y;
}
// </vc-code>

