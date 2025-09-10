predicate ValidInput(N: int, A: int, B: int)
{
  N >= 1 && A >= 1 && A <= B && B <= 36
}

function digitSum(n: int): int
  requires n >= 0
{
  if n == 0 then 0
  else (n % 10) + digitSum(n / 10)
}

function sumInRange(N: int, A: int, B: int): int
  requires N >= 0
  requires A >= 1 && A <= B
{
  if N == 0 then 0
  else if A <= digitSum(N) <= B then N + sumInRange(N-1, A, B)
  else sumInRange(N-1, A, B)
}

// <vc-helpers>
function sumInRangeIter(N: int, A: int, B: int): int
  requires N >= 0
  requires A >= 1 && A <= B && B <= 36
  decreases N
{
  if N == 0 then 0
  else if A <= digitSum(N) <= B then N + sumInRangeIter(N-1, A, B)
  else sumInRangeIter(N-1, A, B)
}
// Introduce a helper function for the sumInRange calculation within the loop
// This helps to prove the loop invariant more easily.
function sumInRangePrefix(initialN: int, currentN: int, A: int, B: int): int
  requires initialN >= 0
  requires currentN >= 0
  requires currentN <= initialN
  requires A >= 1 && A <= B
{
  if initialN == currentN then 0
  else if A <= digitSum(initialN) <= B then initialN + sumInRangePrefix(initialN - 1, currentN, A, B)
  else sumInRangePrefix(initialN - 1, currentN, A, B)
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, A: int, B: int) returns (result: int)
  requires ValidInput(N, A, B)
  ensures result == sumInRange(N, A, B)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  // The 'result' variable is already declared as a return parameter.
  // No need to declare it again.
  // var result := 0; // Removing this line fixes the duplicate variable error.
  result := 0; // Initialize the return parameter 'result'
  var currentN := N;

  while currentN > 0
    invariant 0 <= currentN <= N
    invariant result == sumInRangePrefix(N, currentN, A, B)
    decreases currentN
  {
    if A <= digitSum(currentN) <= B {
      result := result + currentN;
    }
    currentN := currentN - 1;
  }
  // After the loop, currentN will be 0.
  // The invariant `result == sumInRangePrefix(N, currentN, A, B)` becomes `result == sumInRangePrefix(N, 0, A, B)`.
  // By definition of `sumInRangePrefix`, `sumInRangePrefix(N, 0, A, B)` is equivalent to `sumInRange(N, A, B)`.
  // Thus, `result == sumInRange(N, A, B)` is established.
  return result;
}
// </vc-code>

