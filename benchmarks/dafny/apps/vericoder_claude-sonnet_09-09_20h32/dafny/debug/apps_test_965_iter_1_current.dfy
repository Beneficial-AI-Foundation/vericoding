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
lemma CountStatusCorrect(statuses: string, status: char, count: int)
    requires count == |seq(i | 0 <= i < |statuses| && statuses[i] == status)|
    ensures count == CountStatus(statuses, status)
{
}

lemma CountProperties(statuses: string)
    ensures CountStatus(statuses, 'I') + CountStatus(statuses, 'A') + CountStatus(statuses, 'F') <= |statuses|
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
    var cnt_I := 0;
    var cnt_A := 0;
    
    var i := 0;
    while i < |statuses|
        invariant 0 <= i <= |statuses|
        invariant cnt_I == |set j | 0 <= j < i && statuses[j] == 'I'|
        invariant cnt_A == |set j | 0 <= j < i && statuses[j] == 'A'|
    {
        if statuses[i] == 'I' {
            cnt_I := cnt_I + 1;
        } else if statuses[i] == 'A' {
            cnt_A := cnt_A + 1;
        }
        i := i + 1;
    }
    
    assert cnt_I == CountStatus(statuses, 'I');
    assert cnt_A == CountStatus(statuses, 'A');
    
    if cnt_I == 0 {
        result := cnt_A;
    } else if cnt_I == 1 {
        result := 1;
    } else {
        result := 0;
    }
}
// </vc-code>

