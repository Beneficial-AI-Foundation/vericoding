Given two bottles where Bottle 1 has capacity A milliliters and currently contains B milliliters,
and Bottle 2 currently contains C milliliters, transfer as much water as possible from Bottle 2
to Bottle 1 and determine how much water remains in Bottle 2.

predicate ValidInput(a: int, b: int, c: int)
{
    1 <= b <= a <= 20 && 1 <= c <= 20
}

function RemainingWater(a: int, b: int, c: int): int
    requires ValidInput(a, b, c)
{
    var availableSpace := a - b;
    var remaining := c - availableSpace;
    if remaining >= 0 then remaining else 0
}

function SplitOnSpaces(s: string): seq<string>
{
    if |s| == 0 then []
    else SplitOnSpacesHelper(s, "", [])
}

function SplitOnSpacesHelper(s: string, current: string, acc: seq<string>): seq<string>
    decreases |s|
{
    if |s| == 0 then
        if |current| > 0 then acc + [current] else acc
    else if s[0] == ' ' then
        if |current| > 0 then
            SplitOnSpacesHelper(s[1..], "", acc + [current])
        else
            SplitOnSpacesHelper(s[1..], "", acc)
    else
        SplitOnSpacesHelper(s[1..], current + [s[0]], acc)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then
        match s[0]
            case '0' => 0 case '1' => 1 case '2' => 2 case '3' => 3 case '4' => 4
            case '5' => 5 case '6' => 6 case '7' => 7 case '8' => 8 case '9' => 9
            case _ => 0
    else
        StringToInt(s[..|s|-1]) * 10 + StringToInt(s[|s|-1..])
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else if n < 10 then 
        match n
            case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4" case 5 => "5"
            case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
            case _ => "0"
    else
        IntToString(n / 10) + IntToString(n % 10)
}

method solve(input: string) returns (result: string)
    requires |input| > 0
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3 ==>
             (forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9') &&
             (forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9') &&
             (forall i :: 0 <= i < |parts[2]| ==> '0' <= parts[2][i] <= '9') &&
             |parts[0]| > 0 && |parts[1]| > 0 && |parts[2]| > 0
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3 ==>
             ValidInput(StringToInt(parts[0]), StringToInt(parts[1]), StringToInt(parts[2]))
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
            var parts := SplitOnSpaces(trimmed);
            var a := StringToInt(parts[0]);
            var b := StringToInt(parts[1]);
            var c := StringToInt(parts[2]);
            result == IntToString(RemainingWater(a, b, c)) + "\n"
{
    var trimmed := input;
    if |trimmed| > 0 && trimmed[|trimmed|-1] == '\n' {
        trimmed := trimmed[..|trimmed|-1];
    }

    var parts := SplitOnSpaces(trimmed);

    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var c := StringToInt(parts[2]);

    var remainingWater := RemainingWater(a, b, c);
    result := IntToString(remainingWater) + "\n";
}
