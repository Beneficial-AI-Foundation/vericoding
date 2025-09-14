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
lemma SetComprehensionSize<T>(range: int, f: int -> T)
    ensures 0 <= range ==> |set i | 0 <= i < range :: f(i)| <= range
{
    if range == 0 {
    } else {
        calc {
            |set i | 0 <= i < range :: f(i)|
            == |set i | 0 <= i < range-1 :: f(i) union {f(range-1)}|;
            <= |set i | 0 <= i < range-1 :: f(i)| + 1;
            <= (range-1) + 1;
            == range;
        }
    }
}

lemma AllDistinctCyclicShiftsBounds(s: string)
    requires ValidInput(s)
    ensures 1 <= |AllDistinctCyclicShifts(s)| <= |s|
{
    assert ApplyShifts(s, 0) == s;
    assert s in AllDistinctCyclicShifts(s);
    assert |AllDistinctCyclicShifts(s)| >= 1;
    
    SetComprehensionSize(|s|, i => ApplyShifts(s, i));
    assert |AllDistinctCyclicShifts(s)| <= |s|;
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
  AllDistinctCyclicShiftsBounds(s);
  result := |AllDistinctCyclicShifts(s)|;
}
// </vc-code>

