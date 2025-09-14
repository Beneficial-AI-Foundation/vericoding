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
predicate Divides(p: nat, q: nat)
requires p > 0 && q > 0
{p * (q / p) == q}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures 1 <= result <= |s|
    ensures result == |AllDistinctCyclicShifts(s)|
// </vc-spec>
// <vc-code>
{
var p : nat := 1;
while (p < |s| && !(Divides(p, |s|) && ApplyShifts(s, p) == s))
invariant 1 <= p <= |s|
invariant forall j | 1 <= j < p :: !(Divides(j, |s|) && ApplyShifts(s, j) == s)
decreases p
{
   p := p + 1;
}
result := p;
}
// </vc-code>

