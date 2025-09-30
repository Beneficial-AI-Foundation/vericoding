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
lemma CardinalityBound<T>(s: set<T>, t: set<T>)
    requires s <= t
    ensures |s| <= |t|
{
    // The proof follows from the fact that if s is a subset of t,
    // then every element in s is also in t, so s cannot have more elements than t.
    // Dafny can usually prove this automatically with a hint about the relationship.
    if s == {} {
        assert |s| == 0;
        assert |s| <= |t|;
    } else if s == t {
        assert |s| == |t|;
    } else {
        // s is a proper subset of t
        var x :| x in t && x !in s;
        var t' := t - {x};
        assert s <= t';
        if s != t' {
            CardinalityBound(s, t');
            assert |s| <= |t'|;
        }
        assert t == t' + {x};
        assert x !in t';
        assert |t| == |t'| + 1;
        assert |s| <= |t|;
    }
}

lemma RangeSetCardinality(n: int)
    requires n >= 0
    ensures |set i {:trigger i >= 0} | 0 <= i < n| == n
{
    if n == 0 {
        assert (set i {:trigger i >= 0} | 0 <= i < n) == {};
    } else {
        var s := set i {:trigger i >= 0} | 0 <= i < n;
        var s' := set i {:trigger i >= 0} | 0 <= i < n-1;
        assert s == s' + {n-1};
        assert n-1 !in s';
        RangeSetCardinality(n-1);
        assert |s'| == n-1;
        assert |s| == |s'| + 1;
    }
}

lemma CountStatusCorrect(statuses: string, status: char, count: int)
    requires count == |set i {:trigger statuses[i]} | 0 <= i < |statuses| && statuses[i] == status|
    ensures count >= 0
    ensures count <= |statuses|
{
    var indices := set i {:trigger statuses[i]} | 0 <= i < |statuses| && statuses[i] == status;
    var all_indices := set i {:trigger i >= 0} | 0 <= i < |statuses|;
    
    assert forall x :: x in indices ==> x in all_indices;
    assert indices <= all_indices;
    CardinalityBound(indices, all_indices);
    assert |indices| <= |all_indices|;
    
    RangeSetCardinality(|statuses|);
    assert |all_indices| == |statuses|;
    assert count == |indices|;
}

lemma CountLoop(statuses: string, status: char, k: int, count: int)
    requires 0 <= k <= |statuses|
    requires count == |set i {:trigger statuses[i]} | 0 <= i < k && statuses[i] == status|
    ensures count >= 0
    ensures count <= k
{
    var indices := set i {:trigger statuses[i]} | 0 <= i < k && statuses[i] == status;
    var all_indices := set i {:trigger i >= 0} | 0 <= i < k;
    
    assert forall x :: x in indices ==> x in all_indices;
    assert indices <= all_indices;
    CardinalityBound(indices, all_indices);
    assert |indices| <= |all_indices|;
    
    RangeSetCardinality(k);
    assert |all_indices| == k;
    assert count == |indices|;
}

lemma SetComprehensionAdd(statuses: string, status: char, i: int)
    requires 0 <= i < |statuses|
    ensures statuses[i] == status ==> 
        |set j {:trigger statuses[j]} | 0 <= j < i+1 && statuses[j] == status| == 
        |set j {:trigger statuses[j]} | 0 <= j < i && statuses[j] == status| + 1
    ensures statuses[i] != status ==> 
        |set j {:trigger statuses[j]} | 0 <= j < i+1 && statuses[j] == status| == 
        |set j {:trigger statuses[j]} | 0 <= j < i && statuses[j] == status|
{
    var before := set j {:trigger statuses[j]} | 0 <= j < i && statuses[j] == status;
    var after := set j {:trigger statuses[j]} | 0 <= j < i+1 && statuses[j] == status;
    
    if statuses[i] == status {
        assert after == before + {i};
        assert i !in before;
        assert |after| == |before| + 1;
    } else {
        assert after == before;
    }
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
        invariant cnt_I == |set j {:trigger statuses[j]} | 0 <= j < i && statuses[j] == 'I'|
        invariant cnt_A == |set j {:trigger statuses[j]} | 0 <= j < i && statuses[j] == 'A'|
    {
        var old_cnt_I := cnt_I;
        var old_cnt_A := cnt_A;
        
        if statuses[i] == 'I' {
            SetComprehensionAdd(statuses, 'I', i);
            cnt_I := cnt_I + 1;
            SetComprehensionAdd(statuses, 'A', i);
        } else if statuses[i] == 'A' {
            SetComprehensionAdd(statuses, 'A', i);
            cnt_A := cnt_A + 1;
            SetComprehensionAdd(statuses, 'I', i);
        } else {
            SetComprehensionAdd(statuses, 'I', i);
            SetComprehensionAdd(statuses, 'A', i);
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

