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
predicate isValidInteger(s: string) {
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9') && (|s| == 1 || s[0] != '0')
}

function stringToInt(s: string): int
    requires isValidInteger(s)
{
    if |s| == 0 then 0
    else
        var digit := s[0] as int - '0' as int;
        digit * pow10(|s| - 1) + stringToInt(s[1..])
}

function pow10(n: nat): int
{
    if n == 0 then 1 else 10 * pow10(n - 1)
}

lemma pow10_positive(n: nat)
    ensures pow10(n) > 0
{
}

function intToString(n: int): string
    requires n >= 0
{
    if n < 10 then [('0' as int + n) as char]
    else intToString(n / 10) + [('0' as int + n % 10) as char]
}

function split(s: string, sep: char): seq<string>
    ensures |split(s, sep)| >= 1
{
    if |s| == 0 then [""]
    else if s[0] == sep then [""] + split(s[1..], sep)
    else
        var firstSplit := split(s[1..], sep);
        [s[0] + firstSplit[0]] + firstSplit[1..]
}

function replace(s: string, old_str: string, new_str: string): string
{
    if |s| < |old_str| then s
    else if s[0..|old_str|] == old_str then new_str + replace(s[|old_str|..], old_str, new_str)
    else [s[0]] + replace(s[1..], old_str, new_str)
}
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
    var cleanedInput := replace(input, "\n", "");
    var parts := split(cleanedInput, ' ');
    var trainFare := stringToInt(parts[0]);
    var busFare := stringToInt(parts[1]);
    var total := TotalCost(trainFare, busFare);
    result := intToString(total) + "\n";
}
// </vc-code>

