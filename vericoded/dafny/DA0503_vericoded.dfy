predicate ValidInput(A: int, B: int, C: int, D: int) {
  A >= 1 && B >= A && C >= 1 && D >= 1
}

predicate NotDivisibleByEither(x: int, C: int, D: int)
  requires C > 0 && D > 0
{
  x % C != 0 && x % D != 0
}

function CountNotDivisible(A: int, B: int, C: int, D: int): int
  requires ValidInput(A, B, C, D)
{
  |set x | A <= x <= B && NotDivisibleByEither(x, C, D)|
}

// <vc-helpers>
function f(x: int, C: int, D: int): int
  requires C > 0 && D > 0
{
  if x < 1 then 0
  else CountNotDivisible(1, x, C, D)
}

lemma FunctionProperty(A: int, B: int, C: int, D: int)
  requires ValidInput(A, B, C, D)
  ensures f(B, C, D) - f(A - 1, C, D) == CountNotDivisible(A, B, C, D)
{
  var setAB := set x | A <= x <= B && NotDivisibleByEither(x, C, D);
  var set1B := set x | 1 <= x <= B && NotDivisibleByEither(x, C, D);
  var set1A := set x | 1 <= x <= A - 1 && NotDivisibleByEither(x, C, D);
  
  assert f(B, C, D) == |set1B|;
  assert f(A - 1, C, D) == |set1A|;
  assert CountNotDivisible(A, B, C, D) == |setAB|;
  
  assert set1B == set1A + setAB;
  assert set1A * setAB == {};
  assert |set1B| == |set1A| + |setAB|;
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int, D: int) returns (result: int)
  requires ValidInput(A, B, C, D)
  ensures result >= 0
  ensures result == f(B, C, D) - f(A - 1, C, D)
// </vc-spec>
// <vc-code>
{
  FunctionProperty(A, B, C, D);
  result := f(B, C, D) - f(A - 1, C, D);
}
// </vc-code>

