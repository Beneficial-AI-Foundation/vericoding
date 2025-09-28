// <vc-preamble>
function lengthSqr(p1: (int, int), p2: (int, int)): int
{
    (p1.0 - p2.0) * (p1.0 - p2.0) + (p1.1 - p2.1) * (p1.1 - p2.1)
}

predicate ValidRotationExists(a: (int, int), b: (int, int), c: (int, int))
{
    var distABSqr := lengthSqr(a, b);
    var distBCSqr := lengthSqr(b, c);
    var dx1 := c.0 - b.0;
    var dy1 := c.1 - b.1;
    var dx2 := b.0 - a.0;
    var dy2 := b.1 - a.1;
    distABSqr == distBCSqr && dx1 * dy2 != dy1 * dx2
}

function parseInputFunc(input: string): seq<int>
    requires |input| > 0
{
    parseInputHelper(input, 0, [], "")
}

function parseInputHelper(input: string, i: int, result: seq<int>, current: string): seq<int>
    requires 0 <= i <= |input|
    decreases |input| - i
{
    if i == |input| then
        if |current| > 0 then result + [stringToInt(current)]
        else result
    else
        var ch := input[i];
        if ch == ' ' || ch == '\n' || ch == '\t' then
            if |current| > 0 then
                parseInputHelper(input, i + 1, result + [stringToInt(current)], "")
            else
                parseInputHelper(input, i + 1, result, "")
        else if ('0' <= ch <= '9') || ch == '-' then
            parseInputHelper(input, i + 1, result, current + [ch])
        else
            parseInputHelper(input, i + 1, result, current)
}

function stringToInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 && s[0] == '-' then 0
    else if s[0] == '-' && |s| > 1 && isDigitString(s[1..]) then -stringToIntHelper(s[1..])
    else if isDigitString(s) then stringToIntHelper(s)
    else 0
}

function isDigitString(s: string): bool
{
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function stringToIntHelper(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 0 then 0
    else if |s| == 1 then charToDigit(s[0])
    else stringToIntHelper(s[..|s|-1]) * 10 + charToDigit(s[|s|-1])
}

function charToDigit(c: char): int
    requires '0' <= c <= '9'
{
    (c as int) - ('0' as int)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): The original GetCoordinates helper calls parseInputFunc(input) without ensuring the precondition `|input| > 0`. This is explicitly stated in the method solve's `requires` clause. By adding `requires |input| > 0` to GetCoordinates, we signal that this precondition should be met whenever the helper is used. */
function GetCoordinates(input: string): seq<(int, int)>
    requires |input| > 0
{
    var parsed := parseInputFunc(input);
    if |parsed| != 6 then
        []
    else
        [(parsed[0], parsed[1]), (parsed[2], parsed[3]), (parsed[4], parsed[5])]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "Yes" || result == "No" || result == ""
    ensures var coords := parseInputFunc(input); 
            |coords| != 6 ==> result == ""
    ensures var coords := parseInputFunc(input);
            |coords| == 6 ==> 
                var a := (coords[0], coords[1]);
                var b := (coords[2], coords[3]);
                var c := (coords[4], coords[5]);
                (ValidRotationExists(a, b, c) ==> result == "Yes") &&
                (!ValidRotationExists(a, b, c) ==> result == "No")
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed an issue where the helper GetCoordinates didn't meet the preconditions of parseInputFunc. */
{
  var parsed := parseInputFunc(input);
  if |parsed| != 6 {
    result := "";
  } else {
    var a := (parsed[0], parsed[1]);
    var b := (parsed[2], parsed[3]);
    var c := (parsed[4], parsed[5]);
    if ValidRotationExists(a, b, c) {
      result := "Yes";
    } else {
      result := "No";
    }
  }
}
// </vc-code>
