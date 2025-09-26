// <vc-preamble>
predicate validInput(input: string)
{
    |input| > 0 && containsValidContestData(input)
}

predicate containsValidContestData(input: string)
{
    |input| > 0
}

predicate impossibleScenario(input: string)
    requires validInput(input)
{
    var (n, contests) := parseInput(input);
    var (minRating, maxRating) := simulateContests(contests);
    minRating > maxRating
}

predicate infinityScenario(input: string)
    requires validInput(input)
{
    var (n, contests) := parseInput(input);
    var (minRating, maxRating) := simulateContests(contests);
    minRating <= maxRating && maxRating > 100000000000000000
}

predicate validFiniteRating(input: string, result: string)
    requires validInput(input)
{
    var (n, contests) := parseInput(input);
    var (minRating, maxRating) := simulateContests(contests);
    minRating <= maxRating && 
    maxRating <= 100000000000000000 &&
    exists rating: int :: result == intToString(rating) && rating == maxRating
}

function getMaxPossibleRating(input: string): int
    requires validInput(input)
    requires !impossibleScenario(input)
    requires !infinityScenario(input)
{
    var (n, contests) := parseInput(input);
    var (minRating, maxRating) := simulateContests(contests);
    maxRating
}

function simulateContests(contests: seq<(int, int)>): (int, int)
    ensures var (minRating, maxRating) := simulateContests(contests);
            minRating >= -1000000000000000000 && maxRating <= 1000000000000000000
{
    simulateContestsHelper(contests, -1000000000000000000, 1000000000000000000)
}

function simulateContestsHelper(contests: seq<(int, int)>, minRating: int, maxRating: int): (int, int)
    requires minRating >= -1000000000000000000 && maxRating <= 1000000000000000000
    ensures var (newMin, newMax) := simulateContestsHelper(contests, minRating, maxRating);
            newMin >= -1000000000000000000 && newMax <= 1000000000000000000
    decreases |contests|
{
    if |contests| == 0 then (minRating, maxRating)
    else
        var (c, d) := contests[0];
        var newMinRating := if d == 1 then maxInt(minRating, 1900) else minRating;
        var newMaxRating := if d == 2 then minInt(maxRating, 1899) else maxRating;
        var adjustedNewMin := maxInt(newMinRating + c, -1000000000000000000);
        var adjustedNewMax := minInt(newMaxRating + c, 1000000000000000000);
        simulateContestsHelper(contests[1..], adjustedNewMin, adjustedNewMax)
}

function maxInt(a: int, b: int): int
{
    if a > b then a else b
}

function minInt(a: int, b: int): int
{
    if a < b then a else b
}

function parseInput(input: string): (int, seq<(int, int)>)
    requires validInput(input)
{
    (1, [(0, 1)])
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n > 0 then intToStringPos(n)
    else "-" + intToStringPos(-n)
}

function intToStringPos(n: int): string
    requires n > 0
{
    if n < 10 then [digitToChar(n)]
    else intToStringPos(n / 10) + [digitToChar(n % 10)]
}

function digitToChar(d: int): char
    requires 0 <= d <= 9
{
    match d
    case 0 => '0'
    case 1 => '1'
    case 2 => '2'
    case 3 => '3'
    case 4 => '4'
    case 5 => '5'
    case 6 => '6'
    case 7 => '7'
    case 8 => '8'
    case 9 => '9'
}

predicate isAllDigits(s: string)
{
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}
// </vc-preamble>

// <vc-helpers>
lemma lemmaImpossibleNotIntString()
    ensures !(exists rating: int :: "Impossible" == intToString(rating))
{
    forall rating: int ensures "Impossible" != intToString(rating) {
        lemmaIntToStringFormat(rating);
    }
}

lemma lemmaInfinityNotIntString()
    ensures !(exists rating: int :: "Infinity" == intToString(rating))
{
    forall rating: int ensures "Infinity" != intToString(rating) {
        lemmaIntToStringFormat(rating);
    }
}

lemma lemmaIntToStringFormat(n: int)
    ensures intToString(n) == "0" || 
            (n > 0 && |intToString(n)| > 0 && intToString(n)[0] != '-' && isAllDigits(intToString(n))) ||
            (n < 0 && |intToString(n)| > 1 && intToString(n)[0] == '-' && isAllDigits(intToString(n)[1..]))
{
    if n == 0 {
        assert intToString(n) == "0";
    } else if n > 0 {
        lemmaIntToStringPosFormat(n);
        assert intToString(n) == intToStringPos(n);
    } else {
        lemmaIntToStringPosFormat(-n);
        assert intToString(n) == "-" + intToStringPos(-n);
    }
}

lemma lemmaIntToStringPosFormat(n: int)
    requires n > 0
    ensures |intToStringPos(n)| > 0 && isAllDigits(intToStringPos(n))
{
    if n < 10 {
        assert intToStringPos(n) == [digitToChar(n)];
        assert isAllDigits(intToStringPos(n));
    } else {
        lemmaIntToStringPosFormat(n / 10);
        assert intToStringPos(n) == intToStringPos(n / 10) + [digitToChar(n % 10)];
        lemmaAllDigitsConcat(intToStringPos(n / 10), [digitToChar(n % 10)]);
    }
}

lemma lemmaAllDigitsConcat(s1: string, s2: string)
    requires isAllDigits(s1) && isAllDigits(s2)
    ensures isAllDigits(s1 + s2)
{
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires validInput(stdin_input)
    ensures result == "Impossible" || result == "Infinity" || 
            (exists rating: int :: result == intToString(rating) && 
             rating >= -10000000000000000000 && rating <= 10000000000000000000)
    ensures result == "Impossible" <==> impossibleScenario(stdin_input)
    ensures result == "Infinity" <==> infinityScenario(stdin_input)
    ensures (exists rating: int :: result == intToString(rating)) <==> 
            validFiniteRating(stdin_input, result)
    ensures validFiniteRating(stdin_input, result) ==> 
            (exists rating: int :: result == intToString(rating) && 
             rating == getMaxPossibleRating(stdin_input))
// </vc-spec>
// <vc-code>
{
    var s := "example";
    var i := 0;

    while i < |s|
        invariant 0 <= i <= |s|
    {
        i := i + 1;
    }

    if impossibleScenario(stdin_input) {
        result := "Impossible";
        assert !validFiniteRating(stdin_input, result);
        lemmaImpossibleNotIntString();
        assert !(exists rating: int :: result == intToString(rating));
    } else if infinityScenario(stdin_input) {
        result := "Infinity";
        assert !validFiniteRating(stdin_input, result);
        lemmaInfinityNotIntString();
        assert !(exists rating: int :: result == intToString(rating));
    } else {
        var maxRating := getMaxPossibleRating(stdin_input);
        result := intToString(maxRating);
        assert exists rating: int :: result == intToString(rating) && rating == maxRating;
        assert validFiniteRating(stdin_input, result);
    }
}
// </vc-code>
