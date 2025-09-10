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
predicate ValidChars(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] in {'0','1','B'}
}

lemma SimulateKeystrokesValid(s: string)
    requires ValidChars(s)
    ensures ValidOutput(SimulateKeystrokes(s))
{
    if |s| == 0 {} else {
        SimulateKeystrokesValid(s[..|s|-1]);
        var prev := SimulateKeystrokes(s[..|s|-1]);
        var lastKey := s[|s|-1];
        if lastKey == 'B' {
            var result := if |prev| > 0 then prev[..|prev|-1] else prev;
        } else {
            var result := prev + [lastKey];
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
    result := SimulateKeystrokes(s);
    SimulateKeystrokesValid(s);
}
// </vc-code>

