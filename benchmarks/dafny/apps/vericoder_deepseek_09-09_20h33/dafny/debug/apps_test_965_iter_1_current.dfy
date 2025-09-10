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
lemma CountStatusLemma(statuses: string, status: char)
    ensures CountStatus(statuses, status) == |set i | 0 <= i < |statuses| && statuses[i] == status|
{
}

lemma ValidInputLemma(n: int, statuses: string)
    requires ValidInput(n, statuses)
    ensures |statuses| == n
    ensures forall i :: 0 <= i < |statuses| ==> statuses[i] in {'A', 'I', 'F'}
{
}

lemma ExpectedResultLemma(statuses: string)
    ensures ExpectedResult(statuses) ==
        if CountStatus(statuses, 'I') == 0 then CountStatus(statuses, 'A')
        else if CountStatus(statuses, 'I') == 1 then 1
        else 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, statuses: string) returns (result: int)
    requires ValidInput(n, statuses)
    ensures result == ExpectedResult(statuses)
// </vc-spec>
// <vc-code>
{
    var count_I := 0;
    var count_A := 0;
    
    var i := 0;
    while i < |statuses|
        invariant 0 <= i <= |statuses|
        invariant count_I == CountStatus(statuses[0..i], 'I')
        invariant count_A == CountStatus(statuses[0..i], 'A')
    {
        if statuses[i] == 'I' {
            count_I := count_I + 1;
        } else if statuses[i] == 'A' {
            count_A := count_A + 1;
        }
        i := i + 1;
    }
    
    if count_I == 0 {
        result := count_A;
    } else if count_I == 1 {
        result := 1;
    } else {
        result := 0;
    }
}
// </vc-code>

