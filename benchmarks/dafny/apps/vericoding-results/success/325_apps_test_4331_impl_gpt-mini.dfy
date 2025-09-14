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

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: string)
    requires ValidInput(N)
    ensures ValidOutput(result)
    ensures result == "Yes\n" <==> ContainsSeven(N)
// </vc-spec>
// <vc-code>
{
  var d1 := N % 10;
  var d2 := (N / 10) % 10;
  var d3 := N / 100;
  if d1 == 7 || d2 == 7 || d3 == 7 {
    result := "Yes\n";
  } else {
    result := "No\n";
  }
  assert ContainsSeven(N) <==> (d1 == 7 || d2 == 7 || d3 == 7);
  assert (result == "Yes\n") <==> ContainsSeven(N);
}
// </vc-code>

