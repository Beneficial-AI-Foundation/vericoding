predicate ValidInput(n: int)
{
    1 <= n <= 16
}

function FactTruthValues(): seq<int>
{
    [1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0]
}

predicate ValidOutput(result: int)
{
    result == 0 || result == 1
}

function ExpectedOutput(n: int): int
    requires ValidInput(n)
{
    FactTruthValues()[n - 1]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidOutput(result)
    ensures result == ExpectedOutput(n)
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    result := 1;
  } else if n == 2 {
    result := 0;
  } else if n == 3 {
    result := 0;
  } else if n == 4 {
    result := 1;
  } else if n == 5 {
    result := 0;
  } else if n == 6 {
    result := 1;
  } else if n == 7 {
    result := 0;
  } else if n == 8 {
    result := 1;
  } else if n == 9 {
    result := 1;
  } else if n == 10 {
    result := 1;
  } else if n == 11 {
    result := 0;
  } else if n == 12 {
    result := 0;
  } else if n == 13 {
    result := 1;
  } else if n == 14 {
    result := 0;
  } else if n == 15 {
    result := 1;
  } else {
    result := 0;
  }
}
// </vc-code>

