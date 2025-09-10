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
function Abs(x: int): int
{
    if x < 0 then -x else x
}

function SumDigitsInSubstring(s: string, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    ensures SumDigitsInSubstring(s, start, end) >= 0
    decreases end - start
{
    if start == end then 0
    else
        var char_val := s[start]; // Renamed 'char' to 'char_val' to avoid conflict with keyword
        if '1' <= char_val <= '9' then
            (char_val as int) - ('0' as int) + SumDigitsInSubstring(s, start + 1, end)
        else
            SumDigitsInSubstring(s, start + 1, end)
}

lemma SumDigitsWellDefined(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    ensures SumDigitsInSubstring(s, start, end) >= 0
    decreases end - start
{
    if start < end {
        var char_val := s[start]; // Renamed 'char' to 'char_val'
        if '1' <= char_val <= '9' {
            var digit := (char_val as int) - ('0' as int);
            assert digit >= 1; // '1' is 49, '0' is 48, so 49-48 = 1.
            SumDigitsWellDefined(s, start + 1, end);
        } else {
            SumDigitsWellDefined(s, start + 1, end);
        }
    }
}


lemma CalculateTorqueHelperLemma(s: string, pivotPos: int, index: int)
    requires 0 <= pivotPos < |s|
    requires 0 <= index <= |s|
    ensures CalculateTorqueHelper(s, pivotPos, index) ==
            (if index >= |s| then 0 else
                (if '1' <= s[index] <= '9' then
                    var weight := (s[index] as int) - ('0' as int);
                    (pivotPos - index) * weight + CalculateTorqueHelper(s, pivotPos, index + 1)
                else
                    CalculateTorqueHelper(s, pivotPos, index + 1)))
{}

lemma {:induction index} CalculateTorqueHelperPositive(s: string, pivotPos: int, index: int)
    requires 0 <= pivotPos < |s|
    requires 0 <= index <= pivotPos
    requires forall k :: index <= k < pivotPos && '1' <= s[k] <= '9' ==> (pivotPos - k) > 0
    ensures forall k :: index <= k < pivotPos && '1' <= s[k] <= '9' ==> (pivotPos - k) * ((s[k] as int) - ('0' as int)) > 0
    ensures CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, pivotPos) >= 0
    decreases pivotPos - index
{
    if index < pivotPos {
        if '1' <= s[index] <= '9' {
            var weight := (s[index] as int) - ('0' as int);
            assert (pivotPos - index) * weight > 0;
            CalculateTorqueHelperPositive(s, pivotPos, index + 1);
            assert CalculateTorqueHelper(s, pivotPos, index + 1) - CalculateTorqueHelper(s, pivotPos, pivotPos) >= 0;
            assert CalculateTorqueHelper(s, pivotPos, index) == (pivotPos - index) * weight + CalculateTorqueHelper(s, pivotPos, index + 1);
            assert CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, pivotPos) == (pivotPos - index) * weight + (CalculateTorqueHelper(s, pivotPos, index + 1) - CalculateTorqueHelper(s, pivotPos, pivotPos));
            assert (CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, pivotPos)) > 0;
        } else {
            CalculateTorqueHelperPositive(s, pivotPos, index + 1);
            assert CalculateTorqueHelper(s, pivotPos, index) == CalculateTorqueHelper(s, pivotPos, index + 1);
            assert CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, pivotPos) == CalculateTorqueHelper(s, pivotPos, index + 1) - CalculateTorqueHelper(s, pivotPos, pivotPos);
            // We need to prove that (CalculateTorqueHelper(s, pivotPos, index + 1) - CalculateTorqueHelper(s, pivotPos, pivotPos)) is positive if applicable
            // This is already handled by the postcondition of the recursive call.
            assert CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, pivotPos) >= 0;
        }
    } else {
        assert index == pivotPos;
        assert CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, pivotPos) == 0;
    }
}

lemma {:induction index} CalculateTorqueHelperNegative(s: string, pivotPos: int, index: int)
    requires 0 <= pivotPos < |s|
    requires pivotPos <= index <= |s| // Changed to include pivotPos
    requires forall k :: pivotPos < k < index && '1' <= s[k] <= '9' ==> (pivotPos - k) < 0
    ensures CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, |s|) <= 0
    decreases |s| - index
{
    if index < |s| {
        if '1' <= s[index] <= '9' {
            var weight := (s[index] as int) - ('0' as int);
            assert (pivotPos - index) * weight < 0;
            CalculateTorqueHelperNegative(s, pivotPos, index + 1);
            assert CalculateTorqueHelper(s, pivotPos, index + 1) - CalculateTorqueHelper(s, pivotPos, |s|) <= 0;
            assert CalculateTorqueHelper(s, pivotPos, index) == (pivotPos - index) * weight + CalculateTorqueHelper(s, pivotPos, index + 1);
            assert CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, |s|) == (pivotPos - index) * weight + (CalculateTorqueHelper(s, pivotPos, index + 1) - CalculateTorqueHelper(s, pivotPos, |s|));
            if (pivotPos - index) * weight == 0 && CalculateTorqueHelper(s, pivotPos, index + 1) - CalculateTorqueHelper(s, pivotPos, |s|) == 0 {
                assert CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, |s|) == 0;
            } else {
                assert CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, |s|) < 0; // It should be strictly less than 0 if a digit contributes
            }
        } else {
            CalculateTorqueHelperNegative(s, pivotPos, index + 1);
            assert CalculateTorqueHelper(s, pivotPos, index) == CalculateTorqueHelper(s, pivotPos, index + 1);
            assert CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, |s|) == CalculateTorqueHelper(s, pivotPos, index + 1) - CalculateTorqueHelper(s, pivotPos, |s|);
            assert CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, |s|) <= 0;
        }
    } else {
        assert index == |s|;
        assert CalculateTorqueHelper(s, pivotPos, index) - CalculateTorqueHelper(s, pivotPos, |s|) == 0;
    }
}

lemma CalculateTorqueTotal(s: string, pivotPos: int)
    requires 0 <= pivotPos < |s|
    ensures CalculateTorque(s, pivotPos) ==
            (CalculateTorqueHelper(s, pivotPos, 0) - CalculateTorqueHelper(s, pivotPos, pivotPos)) +
            (CalculateTorqueHelper(s, pivotPos, pivotPos) - CalculateTorqueHelper(s, pivotPos, |s|))
{
    calc {
        CalculateTorque(s, pivotPos);
        CalculateTorqueHelper(s, pivotPos, 0);
        CalculateTorqueHelper(s, pivotPos, 0) - CalculateTorqueHelper(s, pivotPos, pivotPos) + CalculateTorqueHelper(s, pivotPos, pivotPos);
        (CalculateTorqueHelper(s, pivotPos, 0) - CalculateTorqueHelper(s, pivotPos, pivotPos)) +
        (CalculateTorqueHelper(s, pivotPos, pivotPos) - CalculateTorqueHelper(s, pivotPos, |s|)) +
        CalculateTorqueHelper(s, pivotPos, |s|);
        // Since CalculateTorqueHelper(s, pivotPos, |s|) is 0, this holds.
    }
}
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

    // Apply lemmas to prove properties of torque
    CalculateTorqueTotal(s, pivotPos);
    CalculateTorqueHelperPositive(s, pivotPos, 0);
    CalculateTorqueHelperNegative(s, pivotPos, pivotPos); // Changed pivotPos + 1 to pivotPos

    if torque > 0 {
        return "left";
    } else if torque < 0 {
        return "right";
    } else {
        return "balance";
    }
}
// </vc-code>

