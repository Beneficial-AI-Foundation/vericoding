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

lemma DivLemma(a: int, b: int)
  requires b > 0
  ensures a / b * b <= a < (a / b + 1) * b
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
}
// </vc-code>

