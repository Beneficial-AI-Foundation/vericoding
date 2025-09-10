function CyclicShiftForward(s: string): string
    requires |s| > 0
{
    s[1..] + [s[0]]
}

predicate ValidInput(s: string)
{
    |s| > 0
}

function ApplyShifts(s: string, steps: nat): string
    requires |s| > 0
    decreases steps
{
    if steps == 0 then s
    else CyclicShiftForward(ApplyShifts(s, steps - 1))
}

function AllDistinctCyclicShifts(s: string): set<string>
    requires |s| > 0
{
    set i | 0 <= i < |s| :: ApplyShifts(s, i)
}

// <vc-helpers>
lemma ApplyShiftsModulo(s: string, steps: nat)
    requires |s| > 0
    ensures ApplyShifts(s, steps) == ApplyShifts(s, steps % |s|)
{
    if steps < |s| {
        assert steps % |s| == steps;
    } else {
        var q := steps / |s|;
        var r := steps % |s|;
        assert steps == q * |s| + r;
        ApplyShiftsModuloHelper(s, q, r);
    }
}

lemma ApplyShiftsModuloHelper(s: string, q: nat, r: nat)
    requires |s| > 0
    requires r < |s|
    ensures ApplyShifts(s, q * |s| + r) == ApplyShifts(s, r)
    decreases q
{
    if q == 0 {
        assert q * |s| + r == r;
    } else {
        ApplyShiftsModuloHelper(s, q - 1, r);
        ApplyShiftsCycle(s, (q - 1) * |s| + r);
    }
}

lemma ApplyShiftsCycle(s: string, steps: nat)
    requires |s| > 0
    ensures ApplyShifts(s, steps + |s|) == ApplyShifts(s, steps)
    decreases steps
{
    if steps == 0 {
        ApplyShiftsFullCycle(s);
    } else {
        ApplyShiftsCycle(s, steps - 1);
        assert ApplyShifts(s, steps + |s|) == CyclicShiftForward(ApplyShifts(s, steps + |s| - 1));
        assert ApplyShifts(s, steps + |s| - 1) == ApplyShifts(s, steps - 1);
        assert ApplyShifts(s, steps) == CyclicShiftForward(ApplyShifts(s, steps - 1));
    }
}

lemma ApplyShiftsFullCycle(s: string)
    requires |s| > 0
    ensures ApplyShifts(s, |s|) == s
    decreases |s|
{
    if |s| == 1 {
        assert ApplyShifts(s, 1) == CyclicShiftForward(s);
        assert CyclicShiftForward(s) == s[1..] + [s[0]];
        assert s[1..] == [];
        assert s == [s[0]];
    } else {
        var s' := CyclicShiftForward(s);
        assert |s'| == |s|;
        ApplyShiftsFullCycle(s');
        assert ApplyShifts(s', |s'|) == s';
        assert ApplyShifts(s, |s|) == ApplyShifts(s', |s| - 1);
    }
}

lemma AllDistinctShiftsCardinality(s: string)
    requires |s| > 0
    ensures |AllDistinctCyclicShifts(s)| <= |s|
{
    var shifts := AllDistinctCyclicShifts(s);
    assert shifts == set i | 0 <= i < |s| :: ApplyShifts(s, i);
    
    forall i | 0 <= i < |s|
        ensures ApplyShifts(s, i) in shifts
    {
        assert i in set j | 0 <= j < |s| :: j;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures 1 <= result <= |s|
    ensures result == |AllDistinctCyclicShifts(s)|
// </vc-spec>
// <vc-code>
{
    var shifts: set<string> := {};
    var current := s;
    var count := 0;
    
    while count < |s|
        invariant 0 <= count <= |s|
        invariant current == ApplyShifts(s, count)
        invariant shifts == set i | 0 <= i < count :: ApplyShifts(s, i)
        invariant |shifts| == count
    {
        shifts := shifts + {current};
        current := CyclicShiftForward(current);
        count := count + 1;
    }
    
    assert shifts == AllDistinctCyclicShifts(s);
    result := |shifts|;
}
// </vc-code>

