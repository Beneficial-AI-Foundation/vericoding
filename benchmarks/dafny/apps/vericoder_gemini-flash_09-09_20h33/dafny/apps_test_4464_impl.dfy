predicate ValidInput(A: int, B: int, C: int)
{
  1 <= A <= 100 && 1 <= B <= 100 && 0 <= C < B
}

predicate IsSolvable(A: int, B: int, C: int)
{
  exists i :: 1 <= i < B && (i * (A % B)) % B == C
}

// <vc-helpers>
function Modulo(x: int, m: int): int
  requires m > 0
  ensures 0 <= Modulo(x, m) < m
{
  (x % m + m) % m
}

predicate IsSolvableHelper(A: int, B: int, C: int, i: int)
  requires 1 <= B <= 100
  requires 1 <= i < B
{
  (i * Modulo(A, B)) % B == C
}

lemma IsSolvableUnrolled(A: int, B: int, C: int)
  requires 1 <= B <= 100
  decreases B
{
  if B == 1 then
    assert forall i :: 1 <= i < B :: !IsSolvableHelper(A, B, C, i);
    assert !IsSolvable(A, B, C);
  else if exists i :: 1 <= i < B && IsSolvableHelper(A, B, C, i) then
    assert IsSolvable(A, B, C);
  else
    assert !IsSolvable(A, B, C);
}

method FindSolvable(A: int, B: int, C: int) returns (found: bool)
  requires ValidInput(A, B, C)
  ensures found <==> IsSolvable(A, B, C)
{
  var i := 1;
  while i < B
    invariant 1 <= i <= B
    invariant forall k :: 1 <= k < i :: (k * Modulo(A, B)) % B != C
    decreases B - i
  {
    if (i * Modulo(A, B)) % B == C
    {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: string)
  requires ValidInput(A, B, C)
  ensures result == "YES" <==> IsSolvable(A, B, C)
  ensures result == "NO" || result == "YES"
// </vc-spec>
// <vc-code>
{
  var solvable: bool := FindSolvable(A, B, C);
  if solvable then
    return "YES";
  else
    return "NO";
}
// </vc-code>

