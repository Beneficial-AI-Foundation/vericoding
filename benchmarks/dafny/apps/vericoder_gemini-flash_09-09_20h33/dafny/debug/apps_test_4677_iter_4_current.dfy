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
function SimulateKeystrokesIterative(keystrokes: string) : string
  ensures SimulateKeystrokesIterative(keystrokes) == SimulateKeystrokes(keystrokes)
{
  var result := "";
  for i := 0 to |keystrokes|-1
    invariant 0 <= i <= |keystrokes|
    invariant result == SimulateKeystrokes(keystrokes[..i])
  {
    var key := keystrokes[i];
    if key == 'B' then
      if |result| > 0 then
        result := result[..|result|-1];
    else
      result := result + [key];
  }
  return result;
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
  return SimulateKeystrokesIterative(s);
}
// </vc-code>

