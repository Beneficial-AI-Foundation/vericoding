predicate ValidLeverInput(s: string)
{
    |s| >= 3 &&
    (exists i :: 0 <= i < |s| && s[i] == '^') &&
    (forall i :: 0 <= i < |s| ==> (s[i] == '^' || s[i] == '=' || ('1' <= s[i] <= '9'))) &&
    (forall i, j :: 0 <= i < j < |s| && s[i] == '^' ==> s[j] != '^') &&
    (forall i :: 0 <= i < |s| && s[i] == '^' ==> (i != 0 && i != |s| - 1))
}

function FindPivot(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] == '^'
    requires forall i, j :: 0 <= i < j < |s| && s[i] == '^' ==> s[j] != '^'
    ensures 0 <= FindPivot(s) < |s|
    ensures s[FindPivot(s)] == '^'
    ensures forall j :: 0 <= j < FindPivot(s) ==> s[j] != '^'
{
    FindPivotHelper(s, 0)
}

function FindPivotHelper(s: string, index: int): int
    requires 0 <= index <= |s|
    requires exists i :: index <= i < |s| && s[i] == '^'
    ensures index <= FindPivotHelper(s, index) < |s|
    ensures s[FindPivotHelper(s, index)] == '^'
    ensures forall j :: index <= j < FindPivotHelper(s, index) ==> s[j] != '^'
    decreases |s| - index
{
    if index >= |s| then 0
    else if s[index] == '^' then index
    else FindPivotHelper(s, index + 1)
}

function CalculateTorque(s: string, pivotPos: int): int
    requires 0 <= pivotPos < |s|
{
    CalculateTorqueHelper(s, pivotPos, 0)
}

function CalculateTorqueHelper(s: string, pivotPos: int, index: int): int
    requires 0 <= pivotPos < |s|
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index >= |s| then 0
    else if '1' <= s[index] <= '9' then
        var weight := (s[index] as int) - ('0' as int);
        (pivotPos - index) * weight + CalculateTorqueHelper(s, pivotPos, index + 1)
    else
        CalculateTorqueHelper(s, pivotPos, index + 1)
}

function CalculateTorquePartial(s: string, pivotPos: int, upTo: int): int
    requires 0 <= pivotPos < |s|
    requires 0 <= upTo <= |s|
{
    CalculateTorqueHelper(s, pivotPos, 0) - CalculateTorqueHelper(s, pivotPos, upTo)
}

// <vc-helpers>
// No additional helpers needed - the provided functions are sufficient
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidLeverInput(s)
    ensures result == "left" || result == "right" || result == "balance"
    ensures var pivotPos := FindPivot(s);
            var torque := CalculateTorque(s, pivotPos);
            (torque > 0 ==> result == "left") &&
            (torque < 0 ==> result == "right") &&
            (torque == 0 ==> result == "balance")
// </vc-spec>
// <vc-code>
{
    var pivotPos := FindPivot(s);
    var torque := CalculateTorque(s, pivotPos);
    
    if torque > 0 {
        result := "left";
    } else if torque < 0 {
        result := "right";
    } else {
        result := "balance";
    }
}
// </vc-code>

