predicate ValidInput(N: int) {
  1000 <= N <= 9999
}

function ExtractDigits(N: int): (int, int, int, int)
  requires ValidInput(N)
{
  var d1 := N / 1000;
  var d2 := (N / 100) % 10;
  var d3 := (N / 10) % 10;
  var d4 := N % 10;
  (d1, d2, d3, d4)
}

predicate IsGood(N: int)
  requires ValidInput(N)
{
  var (d1, d2, d3, d4) := ExtractDigits(N);
  (d1 == d2 && d2 == d3) || (d2 == d3 && d3 == d4)
}

// <vc-helpers>
lemma lemma_ValidInput_implies_digits_valid(N: int)
  requires ValidInput(N)
  ensures var (d1, d2, d3, d4) := ExtractDigits(N);
          0 <= d1 <= 9 && 0 <= d2 <= 9 && 0 <= d3 <= 9 && 0 <= d4 <= 9
{
  var d1 := N / 1000;
  var d2 := (N / 100) % 10;
  var d3 := (N / 10) % 10;
  var d4 := N % 10;

  assert 1 <= d1 <= 9; // Since N is between 1000 and 9999
  assert 0 <= d2 <= 9;
  assert 0 <= d3 <= 9;
  assert 0 <= d4 <= 9;
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: string)
  requires ValidInput(N)
  ensures result == "Yes" || result == "No"
  ensures result == "Yes" <==> IsGood(N)
// </vc-spec>
// <vc-code>
{
  var (d1, d2, d3, d4) := ExtractDigits(N);

  if (d1 == d2 && d2 == d3) || (d2 == d3 && d3 == d4) {
    result := "Yes";
  } else {
    result := "No";
  }

  // Proof that result corresponds to IsGood(N)
  // The 'if' statement directly mirrors the definition of IsGood(N).
  // Thus, if the condition is true, result is "Yes" and IsGood(N) is true.
  // If the condition is false, result is "No" and IsGood(N) is false.
  // This implies result == "Yes" <==> IsGood(N).
}
// </vc-code>

