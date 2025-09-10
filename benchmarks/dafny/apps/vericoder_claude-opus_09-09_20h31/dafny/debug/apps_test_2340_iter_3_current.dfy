predicate ValidInput(h: int, n: int, platforms: seq<int>)
{
    h >= 1 && n >= 1 && |platforms| >= n && n > 0 && platforms[0] == h
}

predicate ValidCrystalCount(crystals: int, n: int)
{
    crystals >= 0 && crystals <= n - 1
}

function CountCrystalsNeeded(h: int, platforms: seq<int>): int
  requires |platforms| >= 1
  requires platforms[0] == h
  requires h >= 1
{
    if |platforms| == 1 then 0
    else CountCrystalsNeededUpTo(h, platforms + [0], |platforms| - 1)
}

function CountCrystalsNeededUpTo(h: int, arr: seq<int>, upTo: int): int
  requires |arr| >= 1
  requires 0 <= upTo < |arr|
  requires arr[0] == h
  requires h >= 1
  decreases upTo
{
    if upTo == 0 then 0
    else
        var curPos := SimulatePositionUpTo(h, arr, upTo - 1);
        var prevCrystals := CountCrystalsNeededUpTo(h, arr, upTo - 1);
        if curPos == arr[upTo] then prevCrystals
        else if upTo + 1 < |arr| && arr[upTo + 1] == arr[upTo] - 1 then prevCrystals
        else prevCrystals + 1
}

function SimulatePositionUpTo(h: int, arr: seq<int>, upTo: int): int
  requires |arr| >= 1
  requires 0 <= upTo < |arr|
  requires arr[0] == h
  requires h >= 1
  decreases upTo
{
    if upTo == 0 then h
    else
        var prevPos := SimulatePositionUpTo(h, arr, upTo - 1);
        if prevPos == arr[upTo] then prevPos
        else if upTo + 1 < |arr| && arr[upTo + 1] == arr[upTo] - 1 then arr[upTo] - 1
        else prevPos
}

// <vc-helpers>
function ParseInt(s: string): (result: int, consumed: int)
{
    if |s| == 0 || s[0] < '0' || s[0] > '9' then
        (0, 0)
    else
        var restResult := ParseInt(s[1..]);
        ((s[0] as int - '0' as int) * Power10(restResult.1) + restResult.0, restResult.1 + 1)
}

function Power10(n: nat): nat
{
    if n == 0 then 1 else 10 * Power10(n - 1)
}

function ParseInts(s: string, count: nat): seq<int>
  decreases count
{
    if count == 0 || |s| == 0 then
        []
    else
        var parsed := ParseInt(s);
        var val := parsed.0;
        var consumed := parsed.1;
        if consumed == 0 then
            []
        else if consumed >= |s| then
            [val]
        else
            var rest := s[consumed..];
            if |rest| > 0 && rest[0] == ' ' then
                [val] + ParseInts(rest[1..], count - 1)
            else
                [val] + ParseInts(rest, count - 1)
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToString(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: nat): string
  requires n > 0
  decreases n
{
    if n < 10 then
        [('0' as char + n as char)]
    else
        IntToStringHelper(n / 10) + [('0' as char + (n % 10) as char)]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires |input| > 0
  ensures |result| >= 0
// </vc-spec>
// <vc-code>
{
    var lines := [];
    var currentLine := "";
    var i := 0;
    
    while i < |input|
    {
        if input[i] == '\n' {
            lines := lines + [currentLine];
            currentLine := "";
        } else {
            currentLine := currentLine + [input[i]];
        }
        i := i + 1;
    }
    
    if |currentLine| > 0 {
        lines := lines + [currentLine];
    }
    
    if |lines| < 2 {
        return "0";
    }
    
    var firstLineValues := ParseInts(lines[0], 2);
    if |firstLineValues| < 2 {
        return "0";
    }
    
    var h := firstLineValues[0];
    var n := firstLineValues[1];
    
    if h < 1 || n < 1 {
        return "0";
    }
    
    var platforms := ParseInts(lines[1], n as nat);
    
    if |platforms| < n {
        return "0";
    }
    
    platforms := platforms[..n];
    
    if |platforms| == 0 || platforms[0] != h {
        return "0";
    }
    
    var crystalsNeeded := CountCrystalsNeeded(h, platforms);
    
    result := IntToString(crystalsNeeded);
}
// </vc-code>

