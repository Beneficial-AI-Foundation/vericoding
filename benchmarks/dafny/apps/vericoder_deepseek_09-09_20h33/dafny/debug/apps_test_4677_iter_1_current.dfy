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
lemma SimulateKeystrokesLemma(s: string)
    requires ValidInput(s)
    ensures ValidOutput(SimulateKeystrokes(s))
{
    if |s| == 0 {
        // Base case: empty string has valid output
    } else {
        var prev := SimulateKeystrokes(s[..|s|-1]);
        var lastKey := s[|s|-1];
        SimulateKeystrokesLemma(s[..|s|-1]);
        
        if lastKey == 'B' {
            if |prev| > 0 {
                // Removing last character preserves ValidOutput
                assert forall i :: 0 <= i < |prev|-1 ==> prev[..|prev|-1][i] == prev[i];
            }
        } else {
            // Adding '0' or '1' preserves ValidOutput
            assert lastKey in {'0', '1'};
            assert forall i :: 0 <= i < |prev| ==> (prev + [lastKey])[i] == prev[i];
            assert (prev + [lastKey])[|prev|] == lastKey;
        }
    }
}

lemma SimulateKeystrokesEmpty()
    ensures SimulateKeystrokes("") == ""
{
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
    var stack := new string;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant ValidOutput(stack)
        invariant stack == SimulateKeystrokes(s[..i])
    {
        var c := s[i];
        if c == 'B' {
            if |stack| > 0 {
                stack := stack[..|stack|-1];
            }
        } else {
            stack := stack + [c];
        }
        i := i + 1;
    }
    SimulateKeystrokesLemma(s);
    result := stack;
}
// </vc-code>

