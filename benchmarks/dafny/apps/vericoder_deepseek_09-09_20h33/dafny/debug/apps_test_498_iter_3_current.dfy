predicate ValidInput(n: int, m: int, k: int)
{
    1 <= n <= 10000 && 1 <= m <= 10000 && 1 <= k <= 2 * n * m
}

predicate ValidOutput(n: int, m: int, lane: int, desk: int, side: string)
{
    1 <= lane <= n && 1 <= desk <= m && (side == "L" || side == "R")
}

predicate CorrectSolution(n: int, m: int, k: int, lane: int, desk: int, side: string)
    requires ValidInput(n, m, k)
{
    lane == (k - 1) / (2 * m) + 1 &&
    desk == (k - 1) % (2 * m) / 2 + 1 &&
    (side == "L" <==> (k - 1) % (2 * m) % 2 == 0)
}

// <vc-helpers>
lemma ModLemma(a: int, b: int)
  requires b > 0
  ensures 0 <= a % b < b
{
  // Dafny knows this property of modulus
}

lemma DivLemma(a: int, b: int)
  requires b > 0
  ensures a / b * b <= a < (a / b + 1) * b
{
  // Dafny knows this property of division
}

lemma MaxSeatIndexBound(n: int, m: int, k: int)
  requires ValidInput(n, m, k)
  ensures k - 1 < 2 * n * m
{
  // From ValidInput we know k <= 2 * n * m
  // Since k >= 1, k - 1 >= 0 and k - 1 <= 2 * n * m - 1 < 2 * n * m
}

lemma LaneBound(n: int, m: int, seat_index: int)
  requires 0 <= seat_index < 2 * n * m
  requires m > 0
  ensures 0 <= seat_index / (2 * m) < n
{
  var total_seats := 2 * m;
  assert total_seats > 0;
  assert seat_index / total_seats >= 0;
  // Maximum possible lane index is (2*n*m - 1)/ (2*m) < (2*n*m)/(2*m) = n
  assert seat_index < 2 * n * m;
  calc {
    seat_index / total_seats;
    < (2 * n * m) / total_seats;  // Since seat_index < 2*n*m
    == (2 * n * m) / (2 * m);
    == n;
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (lane: int, desk: int, side: string)
    requires ValidInput(n, m, k)
    ensures ValidOutput(n, m, lane, desk, side)
    ensures CorrectSolution(n, m, k, lane, desk, side)
// </vc-spec>
// <vc-code>
{
  var total_seats := 2 * m;
  var seat_index := k - 1;
  
  lane := seat_index / total_seats + 1;
  desk := (seat_index % total_seats) / 2 + 1;
  
  if (seat_index % total_seats) % 2 == 0 {
    side := "L";
  } else {
    side := "R";
  }
  
  // Prove that lane is within bounds
  assert 1 <= lane <= n by {
    MaxSeatIndexBound(n, m, k);
    LaneBound(n, m, seat_index);
    assert 0 <= seat_index / total_seats < n;
    assert 1 <= seat_index / total_seats + 1 <= n;
  }
}
// </vc-code>

