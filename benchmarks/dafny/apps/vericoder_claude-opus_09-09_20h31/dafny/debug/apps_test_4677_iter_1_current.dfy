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
lemma SimulateKeystrokesPrefix(keystrokes: string, i: nat)
    requires i <= |keystrokes|
    ensures SimulateKeystrokes(keystrokes[..i]) == SimulateKeystrokesHelper(keystrokes, i)
{
    if i == 0 {
        assert keystrokes[..0] == "";
    } else {
        SimulateKeystrokesPrefix(keystrokes, i-1);
        assert keystrokes[..i] == keystrokes[..i-1] + [keystrokes[i-1]];
    }
}

function SimulateKeystrokesHelper(keystrokes: string, i: nat): string
    requires i <= |keystrokes|
{
    if i == 0 then ""
    else
        var prev := SimulateKeystrokesHelper(keystrokes, i-1);
        var lastKey := keystrokes[i-1];
        if lastKey == 'B' then
            if |prev| > 0 then prev[..|prev|-1] else prev
        else
            prev + [lastKey]
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
    result := "";
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result == SimulateKeystrokes(s[..i])
        invariant ValidOutput(result)
    {
        var key := s[i];
        if key == 'B' {
            if |result| > 0 {
                result := result[..|result|-1];
            }
        } else {
            result := result + [key];
        }
        
        assert s[..i+1] == s[..i] + [s[i]];
        i := i + 1;
    }
    
    assert s[..|s|] == s;
}
// </vc-code>

