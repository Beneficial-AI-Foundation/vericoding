predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 10 && forall i :: 0 <= i < |s| ==> s[i] in {'0', '1', 'B'}
}

function SimulateKeystrokes(keystrokes: string): string
{
    if |keystrokes| == 0 then ""
    else 
        var prev := SimulateKeystrokes(keystrokes[..|keystrokes|-1]);
        var lastKey := keystrokes[|keystrokes|-1];
        if lastKey == 'B' then
            if |prev| > 0 then prev[..|prev|-1] else prev
        else
            prev + [lastKey]
}

predicate ValidOutput(result: string)
{
    forall i :: 0 <= i < |result| ==> result[i] in {'0', '1'}
}

// <vc-helpers>
lemma SimulateKeystrokesValid(keystrokes: string)
    requires |keystrokes| <= 10 && forall i :: 0 <= i < |keystrokes| ==> keystrokes[i] in {'0', '1', 'B'}
    ensures ValidOutput(SimulateKeystrokes(keystrokes))
    decreases |keystrokes|
{
    if |keystrokes| == 0 {
    } else {
        var prev := SimulateKeystrokes(keystrokes[..|keystrokes|-1]);
        SimulateKeystrokesValid(keystrokes[..|keystrokes|-1]);
        assert ValidOutput(prev);
        var lastKey := keystrokes[|keystrokes|-1];
        if lastKey == 'B' {
            if |prev| > 0 {
                assert ValidOutput(prev[..|prev|-1]);
            }
        } else {
            assert lastKey in {'0', '1'};
            assert ValidOutput(prev + [lastKey]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(result)
    ensures result == SimulateKeystrokes(s)
// </vc-spec>
// <vc-code>
{
    SimulateKeystrokesValid(s);
    return SimulateKeystrokes(s);
}
// </vc-code>

