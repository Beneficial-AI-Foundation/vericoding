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

// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(result)
    ensures result == SimulateKeystrokes(s)
// </vc-spec>
// <vc-code>
{
  var res := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|;
    invariant res == SimulateKeystrokes(s[..i]);
    invariant ValidOutput(res);
  {
    if s[i] == 'B' {
      if |res| > 0 {
        res := res[..|res|-1];
      }
    } else {
      res := res + [s[i]];
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>

