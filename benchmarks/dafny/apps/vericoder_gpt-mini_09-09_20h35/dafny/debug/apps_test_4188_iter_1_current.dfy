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
lemma ExpectedOutputIsValid(n: int)
  requires ValidInput(n)
  ensures ExpectedOutput(n) == FactTruthValues()[n - 1]
  ensures ExpectedOutput(n) == 0 || ExpectedOutput(n) == 1
{
  var s := FactTruthValues();
  // Show the specific element is either 0 or 1 by case on n
  if n == 1 {
    assert s[0] == 1;
  } else if n == 2 {
    assert s[1] == 0;
  } else if n == 3 {
    assert s[2] == 0;
  } else if n == 4 {
    assert s[3] == 1;
  } else if n == 5 {
    assert s[4] == 0;
  } else if n == 6 {
    assert s[5] == 1;
  } else if n == 7 {
    assert s[6] == 0;
  } else if n == 8 {
    assert s[7] == 1;
  } else if n == 9 {
    assert s[8] == 1;
  } else if n == 10 {
    assert s[9] == 1;
  } else if n == 11 {
    assert s[10] == 0;
  } else if n == 12 {
    assert s[11] == 0;
  } else if n == 13 {
    assert s[12] == 1;
  } else if n == 14 {
    assert s[13] == 0;
  } else if n == 15 {
    assert s[14] == 1;
  } else {
    assert s[15] == 0;
  }
  assert ExpectedOutput(n) == s[n - 1];
  assert s[n - 1] == 0 || s[n - 1] == 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidOutput(result)
    ensures result == ExpectedOutput(n)
// </vc-spec>
// <vc-code>
{
  ExpectedOutputIsValid(n);
  result := ExpectedOutput(n);
}
// </vc-code>

