predicate ValidInput(trainFare: int, busFare: int)
{
    1 <= trainFare <= 100 && 1 <= busFare <= 100 && busFare % 2 == 0
}

function TotalCost(trainFare: int, busFare: int): int
    requires ValidInput(trainFare, busFare)
{
    trainFare + busFare / 2
}

// <vc-helpers>
function split(s: string, delimiter: char): seq<string>
function replace(s: string, old: string, replacement: string): string
function isValidInteger(s: string): bool
function stringToInt(s: string): int
    requires isValidInteger(s)
function intToString(n: int): string

lemma SplitProperties(s: string, delimiter: char)
    ensures var parts := split(s, delimiter);
            forall i :: 0 <= i < |parts| ==> |parts[i]| >= 0

lemma IntToStringProperties(n: int)
    ensures |intToString(n)| > 0
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires exists i :: 0 <= i < |input| && input[i] == ' '
    requires var parts := split(replace(input, "\n", ""), ' '); 
             |parts| >= 2 && 
             isValidInteger(parts[0]) && 
             isValidInteger(parts[1])
    requires var parts := split(replace(input, "\n", ""), ' ');
             var trainFare := stringToInt(parts[0]);
             var busFare := stringToInt(parts[1]);
             ValidInput(trainFare, busFare)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures var parts := split(replace(input, "\n", ""), ' ');
            var trainFare := stringToInt(parts[0]);
            var busFare := stringToInt(parts[1]);
            result == intToString(TotalCost(trainFare, busFare)) + "\n"
// </vc-spec>
// <vc-code>
{
    var cleanInput := replace(input, "\n", "");
    var parts := split(cleanInput, ' ');
    var trainFare := stringToInt(parts[0]);
    var busFare := stringToInt(parts[1]);
    var total := TotalCost(trainFare, busFare);
    result := intToString(total) + "\n";
}
// </vc-code>

