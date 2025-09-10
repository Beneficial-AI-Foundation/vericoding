predicate ValidInput(n: int, m: int)
{
  n > 0 && n <= 10000 && m > 1 && m <= 10
}

function MinMoves(n: int): int
  requires n > 0
{
  if n % 2 == 0 then n / 2 else n / 2 + 1
}

predicate ValidMoveCount(n: int, k: int)
  requires n > 0
{
  MinMoves(n) <= k <= n
}

predicate IsValidSolution(n: int, m: int, result: int)
  requires ValidInput(n, m)
{
  result == -1 || (result > 0 && result % m == 0 && ValidMoveCount(n, result))
}

predicate NoSmallerSolution(n: int, m: int, result: int)
  requires ValidInput(n, m)
{
  result == -1 ==> forall k :: (MinMoves(n) <= k <= n) ==> k % m != 0
}

predicate IsMinimalSolution(n: int, m: int, result: int)
  requires ValidInput(n, m)
{
  result != -1 ==> forall k :: (MinMoves(n) <= k <= n && k < result) ==> k % m != 0
}

// <vc-helpers>
function find_minimal_multiple(n: int, m: int): int
  requires n > 0 && m > 0
  ensures (exists k :: MinMoves(n) <= k <= n && k % m == 0) ==> (MinMoves(n) <= find_minimal_multiple(n, m) <= n && find_minimal_multiple(n, m) % m == 0 && (forall k_prime :: MinMoves(n) <= k_prime < find_minimal_multiple(n, m) ==> k_prime % m != 0))
  ensures (forall k :: MinMoves(n) <= k <= n ==> k % m != 0) ==> find_minimal_multiple(n, m) == -1
{
  var min_moves := MinMoves(n);
  if MinMoves(n) > n then // Edge case where the range is empty or invalid
    -1
  else if m == 1 then // Optimization for m=1, where any k is a multiple
    min_moves
  else
  (
    var start_value := min_moves;
    while (start_value <= n && start_value % m != 0)
      decreases n - start_value
      invariant min_moves <= start_value
      invariant forall k_prime :: min_moves <= k_prime < start_value ==> k_prime % m != 0
    {
      start_value := start_value + 1;
    }
    if start_value > n then
      -1 // No multiple of m found in the range
    else
      start_value
  )
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures IsValidSolution(n, m, result)
  ensures NoSmallerSolution(n, m, result)
  ensures IsMinimalSolution(n, m, result)
// </vc-spec>
// <vc-code>
{
  result := find_minimal_multiple(n, m);
}
// </vc-code>

