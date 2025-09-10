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
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method solve(n: int, statuses: string) returns (result: int)
    requires ValidInput(n, statuses)
    ensures result == ExpectedResult(statuses)
// </vc-spec>
// <vc-code>
{
  var cntA := 0;
  var cntI := 0;
  var i := 0;
  while i < |statuses|
    invariant 0 <= i <= |statuses|;
    invariant cntA == |set j | 0 <= j < i && statuses[j] == 'A'|;
    invariant cntI == |set j | 0 <= j < i && statuses[j] == 'I'|;
  {
    if statuses[i] == 'A' {
      cntA := cntA + 1;
    } else if statuses[i] == 'I' {
      cntI := cntI + 1;
    }
    i := i + 1;
  }

  if cntI == 0 {
    result := cntA;
  } else if cntI == 1 {
    result := 1;
  } else {
    result := 0;
  }
}
// </vc-code>

