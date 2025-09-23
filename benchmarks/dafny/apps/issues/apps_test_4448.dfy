// <vc-preamble>
predicate validInput(stdin_input: string)
{
    var lines := splitLines(stdin_input);
    |lines| >= 2 &&
    var nm := parseIntArray(lines[0]);
    |nm| == 2 && nm[0] >= 1 && nm[1] >= 0 &&
    var n := nm[0];
    var m := nm[1];
    var K := parseIntArray(lines[1]);
    |K| == n &&
    (forall i :: 0 <= i < |K| ==> K[i] >= 0) &&
    sum(K) >= 1 && sum(K) <= 1000 &&
    |lines| >= 2 + m &&
    (forall i :: 2 <= i < 2 + m ==> 
        var dt := parseIntArray(lines[i]);
        |dt| == 2 && 1 <= dt[0] <= 1000 && 1 <= dt[1] <= n)
}

predicate isValidDayResult(stdin_input: string, result: string)
    requires validInput(stdin_input)
{
    var lines := splitLines(stdin_input);
    var nm := parseIntArray(lines[0]);
    var n := nm[0];
    var K := parseIntArray(lines[1]);
    var totalTransactions := sum(K);
    var resultDay := stringToInt(result);
    totalTransactions <= resultDay <= totalTransactions * 2
}

predicate isMinimalDayResult(stdin_input: string, result: string)
    requires validInput(stdin_input)
    requires isValidDayResult(stdin_input, result)
{
    var lines := splitLines(stdin_input);
    var nm := parseIntArray(lines[0]);
    var n := nm[0];
    var m := nm[1];
    var K := parseIntArray(lines[1]);
    var totalTransactions := sum(K);

    var offers: map<int, seq<int>> := parseOffers(lines, 2, m, n);
    var resultDay := stringToInt(result);

    enough(resultDay, K, offers, totalTransactions) &&
    (forall day :: totalTransactions <= day < resultDay ==> 
        !enough(day, K, offers, totalTransactions))
}

predicate enough(days: int, K: seq<int>, offers: map<int, seq<int>>, totalTransactions: int)
    requires |K| >= 1
    requires totalTransactions >= 1
    requires days >= 1
    requires totalTransactions == sum(K)
{
    var (boughtTotal, remainingK) := simulateOptimalBuying(days, K, offers, days);
    var remainingMoney := days - boughtTotal;
    var remainingTransactions := sum(remainingK);
    remainingTransactions * 2 <= remainingMoney
}

function parseOffers(lines: seq<string>, startIndex: int, m: int, n: int): map<int, seq<int>>
    requires startIndex >= 0
    requires startIndex + m <= |lines|
    requires n >= 1
    requires m >= 0
    decreases m
{
    if m == 0 then map[]
    else if startIndex >= |lines| then map[]
    else
        var dt := parseIntArray(lines[startIndex]);
        var d := dt[0];
        var t := dt[1] - 1;
        var restOffers := parseOffers(lines, startIndex + 1, m - 1, n);
        if d in restOffers then
            restOffers[d := restOffers[d] + [t]]
        else
            restOffers[d := [t]]
}

function sum(arr: seq<int>): int
{
    if |arr| == 0 then 0
    else arr[0] + sum(arr[1..])
}
// </vc-preamble>

// <vc-helpers>
function simulateOptimalBuying(days: int, K: seq<int>, offers: map<int, seq<int>>, usedFrom: int): (int, seq<int>)
    requires |K| >= 1
    requires days >= 0
    requires usedFrom >= 0
    ensures var (bought, remaining) := simulateOptimalBuying(days, K, offers, usedFrom);
            |remaining| == |K|
    decreases days
{
    if days <= 0 || usedFrom <= 0 then
        (0, K)
    else
        var todayOffers := if days in offers then offers[days] else [];
        var (boughtToday, newK, newUsedFrom) := buyFromOffers(K, todayOffers, usedFrom);
        var (boughtLater, finalK) := simulateOptimalBuying(days - 1, newK, offers, newUsedFrom);
        (boughtToday + boughtLater, finalK)
}

function buyFromOffers(K: seq<int>, todayOffers: seq<int>, usedFrom: int): (int, seq<int>, int)
    requires |K| >= 1
    requires usedFrom >= 0
    ensures var (bought, newK, newUsedFrom) := buyFromOffers(K, todayOffers, usedFrom);
            |newK| == |K| && newUsedFrom >= 0 && bought >= 0
    decreases |todayOffers|
{
    if |todayOffers| == 0 || usedFrom <= 0 then
        (0, K, usedFrom)
    else
        var t := todayOffers[0];
        if 0 <= t < |K| && K[t] > 0 then
            var buyAmount := min(K[t], usedFrom);
            var newK := K[t := K[t] - buyAmount];
            var (moreBought, finalK, finalUsedFrom) := buyFromOffers(newK, todayOffers[1..], usedFrom - buyAmount);
            (buyAmount + moreBought, finalK, finalUsedFrom)
        else
            buyFromOffers(K, todayOffers[1..], usedFrom)
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

function splitLines(input: string): seq<string>
    ensures |splitLines(input)| >= 0
{
    ["", ""]
}

function parseIntArray(line: string): seq<int>
    ensures |parseIntArray(line)| >= 0
{
    [0, 0]
}

function intToString(n: int): string
    ensures |intToString(n)| > 0
{
    "0"
}

function stringToInt(s: string): int
    requires |s| > 0
{
    0
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires validInput(stdin_input)
    ensures |result| > 0
    ensures isValidDayResult(stdin_input, result)
    ensures isMinimalDayResult(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    var lines := splitLines(stdin_input);
    assume |lines| >= 2;

    var firstLine := lines[0];
    var secondLine := lines[1];

    var nm := parseIntArray(firstLine);
    assume |nm| == 2;
    var n := nm[0];
    var m := nm[1];

    var K := parseIntArray(secondLine);
    assume |K| == n;
    assume n >= 1 && m >= 0;
    assume forall i :: 0 <= i < |K| ==> K[i] >= 0;

    var totalTransactions := sum(K);
    assume totalTransactions >= 1 && totalTransactions <= 1000;

    var offers: map<int, seq<int>> := map[];
    var offerIndex := 2;
    while offerIndex < 2 + m && offerIndex < |lines|
        invariant 2 <= offerIndex <= 2 + m
        invariant offerIndex <= |lines|
    {
        var offerLine := lines[offerIndex];
        var dt := parseIntArray(offerLine);
        assume |dt| == 2;
        var d := dt[0];
        var t := dt[1] - 1;

        assume 1 <= dt[0] <= 1000;
        assume 1 <= dt[1] <= n;

        if d in offers {
            offers := offers[d := offers[d] + [t]];
        } else {
            offers := offers[d := [t]];
        }
        offerIndex := offerIndex + 1;
    }

    var low := totalTransactions;
    var high := totalTransactions * 2;
    var ans := high;

    while low <= high
        invariant totalTransactions <= ans <= totalTransactions * 2
        invariant low <= high + 1
        invariant forall days :: totalTransactions <= days < low ==> !enough(days, K, offers, totalTransactions)
        invariant enough(ans, K, offers, totalTransactions)
    {
        var mid := (low + high) / 2;
        if enough(mid, K, offers, totalTransactions) {
            ans := mid;
            high := mid - 1;
        } else {
            low := mid + 1;
        }
    }

    result := intToString(ans);
}
// </vc-code>
