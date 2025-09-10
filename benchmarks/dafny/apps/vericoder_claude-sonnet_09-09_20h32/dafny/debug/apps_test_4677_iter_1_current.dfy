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
lemma SimulateKeystrokesValidOutput(s: string)
    requires ValidInput(s)
    ensures ValidOutput(SimulateKeystrokes(s))
{
    if |s| == 0 {
    } else {
        SimulateKeystrokesValidOutput(s[..|s|-1]);
        var prev := SimulateKeystrokes(s[..|s|-1]);
        var lastKey := s[|s|-1];
        if lastKey == 'B' {
            if |prev| > 0 {
                assert SimulateKeystrokes(s) == prev[..|prev|-1];
            } else {
                assert SimulateKeystrokes(s) == prev;
            }
        } else {
            assert SimulateKeystrokes(s) == prev + [lastKey];
        }
    }
}

lemma SimulateKeystrokesIncremental(s: string, i: int)
    requires ValidInput(s)
    requires 0 <= i < |s|
    ensures SimulateKeystrokes(s[..i+1]) == 
        (var prev := SimulateKeystrokes(s[..i]);
         var key := s[i];
         if key == 'B' then
             if |prev| > 0 then prev[..|prev|-1] else prev
         else
             prev + [key])
{
    assert s[..i+1] == s[..i] + [s[i]];
    assert s[..i+1][..|s[..i+1]|-1] == s[..i];
    assert s[..i+1][|s[..i+1]|-1] == s[i];
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
        invariant ValidOutput(result)
        invariant result == SimulateKeystrokes(s[..i])
    {
        var key := s[i];
        if key == 'B' {
            if |result| > 0 {
                result := result[..|result|-1];
            }
        } else {
            result := result + [key];
        }
        
        SimulateKeystrokesIncremental(s, i);
        i := i + 1;
    }
    
    assert s[..|s|] == s;
    SimulateKeystrokesValidOutput(s);
}
// </vc-code>

