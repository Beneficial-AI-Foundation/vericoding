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
    requires count == |set i | 0 <= i < |statuses| && statuses[i] == status|
    ensures count == CountStatus(statuses, status)
{
}

lemma CountProperties(statuses: string)
    ensures CountStatus(statuses, 'I') + CountStatus(statuses, 'A') + CountStatus(statuses, 'F') <= |statuses|
{
    var setI := set i {:trigger statuses[i]} | 0 <= i < |statuses| && statuses[i] == 'I';
    var setA := set i {:trigger statuses[i]} | 0 <= i < |statuses| && statuses[i] == 'A';
    var setF := set i {:trigger statuses[i]} | 0 <= i < |statuses| && statuses[i] == 'F';
    var allIndices := set i | 0 <= i < |statuses|;
    
    assert setI <= allIndices;
    assert setA <= allIndices;
    assert setF <= allIndices;
    assert setI * setA == {};
    assert setI * setF == {};
    assert setA * setF == {};
}

lemma SetIncrementLemma(statuses: string, i: int, status: char)
    requires 0 <= i < |statuses|
    requires statuses[i] == status
    ensures |set j {:trigger statuses[j]} | 0 <= j < i+1 && statuses[j] == status| == |set j {:trigger statuses[j]} | 0 <= j < i && statuses[j] == status| + 1
{
    var oldSet := set j {:trigger statuses[j]} | 0 <= j < i && statuses[j] == status;
    var newSet := set j {:trigger statuses[j]} | 0 <= j < i+1 && statuses[j] == status;
    assert newSet == oldSet + {i};
    assert i !in oldSet;
}

lemma SetNoIncrementLemma(statuses: string, i: int, status: char)
    requires 0 <= i < |statuses|
    requires statuses[i] != status
    ensures |set j {:trigger statuses[j]} | 0 <= j < i+1 && statuses[j] == status| == |set j {:trigger statuses[j]} | 0 <= j < i && statuses[j] == status|
{
    var oldSet := set j {:trigger statuses[j]} | 0 <= j < i && statuses[j] == status;
    var newSet := set j {:trigger statuses[j]} | 0 <= j < i+1 && statuses[j] == status;
    assert newSet == oldSet;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, statuses: string) returns (result: int)
    requires ValidInput(n, statuses)
    ensures result == ExpectedResult(statuses)
// </vc-spec>
// <vc-code>
{
    CountProperties(statuses);
    
    var cnt_I := 0;
    var cnt_A := 0;
    
    var i := 0;
    while i < |statuses|
        invariant 0 <= i <= |statuses|
        invariant cnt_I == |set j {:trigger statuses[j]} | 0 <= j < i && statuses[j] == 'I'|
        invariant cnt_A == |set j {:trigger statuses[j]} | 0 <= j < i && statuses[j] == 'A'|
    {
        if statuses[i] == 'I' {
            SetIncrementLemma(statuses, i, 'I');
            SetNoIncrementLemma(statuses, i, 'A');
            cnt_I := cnt_I + 1;
        } else if statuses[i] == 'A' {
            SetIncrementLemma(statuses, i, 'A');
            SetNoIncrementLemma(statuses, i, 'I');
            cnt_A := cnt_A + 1;
        } else {
            SetNoIncrementLemma(statuses, i, 'I');
            SetNoIncrementLemma(statuses, i, 'A');
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

