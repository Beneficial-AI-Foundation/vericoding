predicate ValidInput(n: int, a: string, b: string)
{
    n > 0 && |a| == 2 * n && |b| == 2 * n &&
    (forall i :: 0 <= i < |a| ==> a[i] == '0' || a[i] == '1') &&
    (forall i :: 0 <= i < |b| ==> b[i] == '0' || b[i] == '1')
}

function CountPositions(a: string, b: string, ac: char, bc: char, len: int): int
    requires len >= 0 && len <= |a| && len <= |b|
    requires ac == '0' || ac == '1'
    requires bc == '0' || bc == '1'
{
    |set i | 0 <= i < len && a[i] == ac && b[i] == bc|
}

function ComputeGameOutcome(t00: int, t01: int, t10: int, t11: int): int
{
    t11 % 2 + (t10 - t01 + 1 - t11 % 2) / 2
}

predicate CorrectOutcome(result: string, d: int)
{
    (d > 0 ==> result == "First") &&
    (d < 0 ==> result == "Second") &&
    (d == 0 ==> result == "Draw")
}

// <vc-helpers>
lemma CountPositionsSum(a: string, b: string, len: int)
    requires len >= 0 && len <= |a| && len <= |b|
    requires forall i :: 0 <= i < |a| ==> a[i] == '0' || a[i] == '1'
    requires forall i :: 0 <= i < |b| ==> b[i] == '0' || b[i] == '1'
    ensures CountPositions(a, b, '0', '0', len) + 
            CountPositions(a, b, '0', '1', len) + 
            CountPositions(a, b, '1', '0', len) + 
            CountPositions(a, b, '1', '1', len) == len
{
    var s00 := set i | 0 <= i < len && a[i] == '0' && b[i] == '0';
    var s01 := set i | 0 <= i < len && a[i] == '0' && b[i] == '1';
    var s10 := set i | 0 <= i < len && a[i] == '1' && b[i] == '0';
    var s11 := set i | 0 <= i < len && a[i] == '1' && b[i] == '1';
    
    assert forall i :: 0 <= i < len ==> i in s00 || i in s01 || i in s10 || i in s11;
    assert s00 !! s01 !! s10 !! s11;
}

lemma CountPositionsIncrease(a: string, b: string, ac: char, bc: char, i: int)
    requires 0 <= i < |a| && i < |b|
    requires ac == '0' || ac == '1'
    requires bc == '0' || bc == '1'
    ensures a[i] == ac && b[i] == bc ==> 
        CountPositions(a, b, ac, bc, i + 1) == CountPositions(a, b, ac, bc, i) + 1
    ensures a[i] != ac || b[i] != bc ==> 
        CountPositions(a, b, ac, bc, i + 1) == CountPositions(a, b, ac, bc, i)
{
    var s1 := set j | 0 <= j < i + 1 && a[j] == ac && b[j] == bc;
    var s0 := set j | 0 <= j < i && a[j] == ac && b[j] == bc;
    
    if a[i] == ac && b[i] == bc {
        assert s1 == s0 + {i};
        assert |s1| == |s0| + 1;
    } else {
        assert s1 == s0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: string, b: string) returns (result: string)
    requires ValidInput(n, a, b)
    ensures result == "First" || result == "Second" || result == "Draw"
    ensures (exists t00, t01, t10, t11: int ::
        t00 >= 0 && t01 >= 0 && t10 >= 0 && t11 >= 0 &&
        t00 + t01 + t10 + t11 == 2 * n &&
        t00 == CountPositions(a, b, '0', '0', 2 * n) &&
        t01 == CountPositions(a, b, '0', '1', 2 * n) &&
        t10 == CountPositions(a, b, '1', '0', 2 * n) &&
        t11 == CountPositions(a, b, '1', '1', 2 * n) &&
        CorrectOutcome(result, ComputeGameOutcome(t00, t01, t10, t11)))
// </vc-spec>
// <vc-code>
{
    var t00 := 0;
    var t01 := 0;
    var t10 := 0;
    var t11 := 0;
    
    var i := 0;
    while i < 2 * n
        invariant 0 <= i <= 2 * n
        invariant t00 == CountPositions(a, b, '0', '0', i)
        invariant t01 == CountPositions(a, b, '0', '1', i)
        invariant t10 == CountPositions(a, b, '1', '0', i)
        invariant t11 == CountPositions(a, b, '1', '1', i)
        invariant t00 >= 0 && t01 >= 0 && t10 >= 0 && t11 >= 0
        invariant t00 + t01 + t10 + t11 == i
    {
        CountPositionsSum(a, b, i);
        
        CountPositionsIncrease(a, b, '0', '0', i);
        CountPositionsIncrease(a, b, '0', '1', i);
        CountPositionsIncrease(a, b, '1', '0', i);
        CountPositionsIncrease(a, b, '1', '1', i);
        
        if a[i] == '0' && b[i] == '0' {
            t00 := t00 + 1;
        } else if a[i] == '0' && b[i] == '1' {
            t01 := t01 + 1;
        } else if a[i] == '1' && b[i] == '0' {
            t10 := t10 + 1;
        } else {
            assert a[i] == '1' && b[i] == '1';
            t11 := t11 + 1;
        }
        
        i := i + 1;
        
        CountPositionsSum(a, b, i);
    }
    
    assert t00 == CountPositions(a, b, '0', '0', 2 * n);
    assert t01 == CountPositions(a, b, '0', '1', 2 * n);
    assert t10 == CountPositions(a, b, '1', '0', 2 * n);
    assert t11 == CountPositions(a, b, '1', '1', 2 * n);
    assert t00 + t01 + t10 + t11 == 2 * n;
    
    var d := ComputeGameOutcome(t00, t01, t10, t11);
    
    if d > 0 {
        result := "First";
    } else if d < 0 {
        result := "Second";
    } else {
        result := "Draw";
    }
    
    assert CorrectOutcome(result, d);
}
// </vc-code>

