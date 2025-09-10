function winner(a: char, b: char): char
{
    if (a, b) == ('R', 'P') || (a, b) == ('P', 'S') || (a, b) == ('S', 'R') then b else a
}

predicate validRPSChar(c: char)
{
    c == 'R' || c == 'P' || c == 'S'
}

predicate validRPSString(s: string)
{
    forall i :: 0 <= i < |s| ==> validRPSChar(s[i])
}

predicate ValidInput(n: int, k: int, s: string)
{
    n > 0 && k >= 0 && |s| == n && validRPSString(s)
}

// <vc-helpers>
function oneStep(s: string): (new_s: string)
  requires |s| > 0 && validRPSString(s)
  ensures |new_s| == (|s| / 2) + (|s| % 2)
  ensures validRPSString(new_s)
{
  var pairs := seq(|s| / 2, i requires 0 <= 2*i < |s| && 2*i+1 < |s| => winner(s[2*i], s[2*i+1]));
  var extra := if |s| % 2 == 1 then [s[|s|-1]] else [];
  pairs + extra
}

function reduce(s: string, k: int): char
  requires k >= 0 && |s| > 0 && validRPSString(s)
  ensures validRPSChar(reduce(s, k))
{
  if k == 0 || |s| == 1 then s[0] else reduce(oneStep(s), k - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: char)
    requires ValidInput(n, k, s)
    ensures validRPSChar(result)
// </vc-spec>
// <vc-code>
{
  return reduce(s, k);
}
// </vc-code>

