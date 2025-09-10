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
function CountStatusChar(s: string, c: char): int
    reads s
    decreases |s|
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountStatusChar(s[1..], c)
}

function ExpectedResultCalc(statuses: string): int
{
    var cnt_I := CountStatusChar(statuses, 'I');
    var cnt_A := CountStatusChar(statuses, 'A');
    if cnt_I == 0 then cnt_A
    else if cnt_I == 1 then 1
    else 0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, statuses: string) returns (result: int)
    requires ValidInput(n, statuses)
    ensures result == ExpectedResult(statuses)
// </vc-spec>
// <vc-code>
{
    var cnt_I := 0;
    var cnt_A := 0;
    var i := 0;

    while i < n
        invariant 0 <= i <= n
        invariant cnt_I == CountStatusChar(statuses[..i], 'I')
        invariant cnt_A == CountStatusChar(statuses[..i], 'A')
    {
        if statuses[i] == 'I' {
            cnt_I := cnt_I + 1;
        } else if statuses[i] == 'A' {
            cnt_A := cnt_A + 1;
        }
        i := i + 1;
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

