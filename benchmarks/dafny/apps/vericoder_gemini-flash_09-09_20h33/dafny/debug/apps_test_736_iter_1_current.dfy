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
  var start_value := (min_moves + m - 1) / m * m; // Smallest multiple of m >= min_moves
  if start_value > n then
    -1 // No multiple of m found in the range
  else
    start_value
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

