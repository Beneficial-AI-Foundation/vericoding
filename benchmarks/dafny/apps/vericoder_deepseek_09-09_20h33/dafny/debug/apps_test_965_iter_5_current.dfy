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
lemma CountStatusSliceLemma(s: string, status: char, i: int)
    requires 0 <= i <= |s|
    ensures CountStatus(s[0..i], status) == |set j | 0 <= j < i && s[j] == status|
{
}

lemma CountStatusCharLemma(s: string, status: char, i: int)
    requires 0 <= i < |s|
    ensures CountStatus(s[0..i+1], status) == CountStatus(s[0..i], status) + (if s[i] == status then 1 else 0)
{
}

lemma CountStatusInvariantLemma(s: string, i: int, status: char)
    requires 0 <= i <= |s|
    ensures CountStatus(s[0..i], status) == |set j | 0 <= j < i && s[j] == status|
{
    CountStatusSliceLemma(s, status, i);
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
        CountStatusInvariantLemma(statuses, i, 'I');
        CountStatusInvariantLemma(statuses, i, 'A');
        
        var char := statuses[i];
        if char == 'I' {
            count_I := count_I + 1;
        } else if char == 'A' {
            count_A := count_A + 1;
        }
        i := i + 1;
        
        CountStatusCharLemma(statuses, 'I', i-1);
        CountStatusCharLemma(statuses, 'A', i-1);
    }
    
    CountStatusInvariantLemma(statuses, i, 'I');
    CountStatusInvariantLemma(statuses, i, 'A');
    
    if count_I == 0 {
        result := count_A;
    } else if count_I == 1 {
        result := 1;
    } else {
        result := 0;
    }
}
// </vc-code>

