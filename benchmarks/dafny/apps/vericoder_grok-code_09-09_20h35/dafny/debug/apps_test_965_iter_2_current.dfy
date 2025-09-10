predicate ValidInput(n: int, statuses: string)
{
    n >= 2 && |statuses| == n && 
    forall i :: 0 <= i < |statuses| ==> statuses[i] in {'A', 'I', 'F'}
}

function CountStatus(statuses: string, status: char): int
{
    |set i | 0 <= i < |statuses| && statuses[i] == status|
}

function ExpectedResult(statuses: string): int
{
    var cnt_I := CountStatus(statuses, 'I');
    var cnt_A := CountStatus(statuses, 'A');
    if cnt_I == 0 then cnt_A
    else if cnt_I == 1 then 1
    else 0
}

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, statuses: string) returns (result: int)
    requires ValidInput(n, statuses)
    ensures result == ExpectedResult(statuses)
// </vc-spec>
// <vc-code>
{
  var cnt_I := 0;
  for i := 0 to |statuses|-1 {
    if statuses[i] == 'I' {
      cnt_I := cnt_I + 1;
    }
  }
  var cnt_A := 0;
  for i := 0 to |statuses|-1 {
    if statuses[i] == 'A' {
      cnt_A := cnt_A + 1;
    }
  }
  if cnt_I == 0 {
    result := cnt_A;
  } else if cnt_I == 1 {
    result := 1;
  } else {
    result := 0;
  }
}
// </vc-code>

