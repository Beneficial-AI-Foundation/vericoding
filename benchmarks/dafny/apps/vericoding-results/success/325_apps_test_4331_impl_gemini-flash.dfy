// <vc-preamble>
predicate ValidInput(N: int) {
    100 <= N <= 999
}

predicate ContainsSeven(N: int) 
    requires ValidInput(N)
{
    (N % 10) == 7 || ((N / 10) % 10) == 7 || (N / 100) == 7
}

predicate ValidOutput(result: string) {
    result == "Yes\n" || result == "No\n"
}
// </vc-preamble>

// <vc-helpers>
  function IsSeven(d: int): bool {
    0 <= d <= 9 && d == 7
  }

// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: string)
    requires ValidInput(N)
    ensures ValidOutput(result)
    ensures result == "Yes\n" <==> ContainsSeven(N)
// </vc-spec>
// <vc-code>
{
  var hasSeven := false;
  var tempN := N;

  // Check the last digit
  if IsSeven(tempN % 10) {
    hasSeven := true;
  }
  tempN := tempN / 10;

  // Check the middle digit
  if !hasSeven && IsSeven(tempN % 10) {
    hasSeven := true;
  }
  tempN := tempN / 10;

  // Check the first digit
  if !hasSeven && IsSeven(tempN % 10) {
    hasSeven := true;
  }

  if hasSeven {
    result := "Yes\n";
  } else {
    result := "No\n";
  }
}

// </vc-code>
