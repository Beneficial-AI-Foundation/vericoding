predicate ValidInput(a: int, b: int)
{
    1 <= a <= 3 && 1 <= b <= 3
}

predicate IsOdd(n: int)
{
    n % 2 == 1
}

predicate ExistsOddProduct(a: int, b: int)
  requires ValidInput(a, b)
{
    exists c :: 1 <= c <= 3 && IsOdd(a * b * c)
}

function ShouldAnswerYes(a: int, b: int): bool
  requires ValidInput(a, b)
{
    a != 2 && b != 2
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: string)
  requires ValidInput(a, b)
  ensures result == (if ShouldAnswerYes(a, b) then "Yes" else "No")
// </vc-spec>
// <vc-code>
{
  if ShouldAnswerYes(a, b) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

