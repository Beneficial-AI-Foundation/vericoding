Simulate a 3-key text editor that processes keystrokes: '0' and '1' append characters,
'B' deletes the rightmost character if the string is non-empty.

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

method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(result)
    ensures result == SimulateKeystrokes(s)
{
    var ans: seq<char> := [];

    for i := 0 to |s|
        invariant forall j :: 0 <= j < |ans| ==> ans[j] in {'0', '1'}
        invariant ans == SimulateKeystrokes(s[..i])
    {
        var c := s[i];
        var prev := ans;

        if c == 'B' {
            if |ans| > 0 {
                ans := ans[..|ans|-1];
            }
        } else {
            ans := ans + [c];
        }

        assert s[..i+1] == s[..i] + [c];
        assert SimulateKeystrokes(s[..i+1]) == 
            (if c == 'B' then
                (if |prev| > 0 then prev[..|prev|-1] else prev)
            else
                prev + [c]);
        assert ans == SimulateKeystrokes(s[..i+1]);
    }

    assert s[..|s|] == s;
    assert ans == SimulateKeystrokes(s);

    result := ans;
}
