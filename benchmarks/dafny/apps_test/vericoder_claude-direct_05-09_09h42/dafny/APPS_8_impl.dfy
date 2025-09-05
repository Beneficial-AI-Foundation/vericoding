// ======= TASK =======
// Given 3 mahjong tiles, find the minimum number of additional tiles needed to form at least one "mentsu" (meld).
// A mentsu is either:
// - Koutsu (triplet): 3 identical tiles (e.g., [1m, 1m, 1m])
// - Shuntsu (sequence): 3 consecutive numbered tiles in the same suit (e.g., [1m, 2m, 3m])
// Each tile is represented as a number (1-9) followed by a suit letter (m/p/s).

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(input: string)
{
    var lines := splitFunc(input, '\n');
    var cards := if |lines| > 0 then splitFunc(lines[0], ' ') else [];
    |lines| > 0 && |cards| == 3 && 
    (forall i :: 0 <= i < |cards| ==> (|cards[i]| >= 2 && 
     '1' <= cards[i][0] <= '9' && cards[i][1] in {'m', 'p', 's'}))
}

predicate ValidOutput(output: string)
{
    output == "0" || output == "1" || output == "2" || output == "3"
}

function GetCards(input: string): seq<string>
{
    var lines := splitFunc(input, '\n');
    if |lines| > 0 then splitFunc(lines[0], ' ') else []
}

predicate HasKoutsu(cards: seq<string>)
{
    var counts := countCards(cards);
    exists i :: 0 <= i < 9 && (counts.0[i] == 3 || counts.1[i] == 3 || counts.2[i] == 3)
}

predicate HasShuntsu(cards: seq<string>)
{
    var counts := countCards(cards);
    seqCheckerFunc(counts.0) == 3 || seqCheckerFunc(counts.1) == 3 || seqCheckerFunc(counts.2) == 3
}

predicate HasPair(cards: seq<string>)
{
    var counts := countCards(cards);
    exists i :: 0 <= i < 9 && (counts.0[i] == 2 || counts.1[i] == 2 || counts.2[i] == 2)
}

function GetBestWindow(cards: seq<string>): int
{
    var counts := countCards(cards);
    var maxWindowSum := seq(7, i requires 0 <= i < 7 => max3(counts.0[i] + counts.0[i+1] + counts.0[i+2],
                                          counts.1[i] + counts.1[i+1] + counts.1[i+2],
                                          counts.2[i] + counts.2[i+1] + counts.2[i+2]));
    if |maxWindowSum| > 0 then seqMax(maxWindowSum) else 0
}

predicate CorrectResult(input: string, output: string)
{
    if !ValidInput(input) then output == "2"
    else
        var cards := GetCards(input);
        var hasKoutsu := HasKoutsu(cards);
        var hasShuntsu := HasShuntsu(cards);
        var hasPair := HasPair(cards);
        var bestWindow := GetBestWindow(cards);

        (output == "0" <==> (hasKoutsu || hasShuntsu)) &&
        (output == "1" <==> (!hasKoutsu && !hasShuntsu && hasPair)) &&
        (output == "2" <==> (!hasKoutsu && !hasShuntsu && !hasPair && bestWindow == 1)) &&
        (output == "3" <==> (!hasKoutsu && !hasShuntsu && !hasPair && bestWindow != 1))
}

// <vc-helpers>
function splitFunc(s: string, delimiter: char): seq<string>
{
    splitHelper(s, delimiter, 0, "", [])
}

function splitHelper(s: string, delimiter: char, index: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index == |s| then
        acc + [current]
    else if s[index] == delimiter then
        splitHelper(s, delimiter, index + 1, "", acc + [current])
    else
        splitHelper(s, delimiter, index + 1, current + [s[index]], acc)
}

function countCards(cards: seq<string>): (seq<int>, seq<int>, seq<int>)
    ensures var result := countCards(cards);
            |result.0| == 9 && |result.1| == 9 && |result.2| == 9
{
    var lm := seq(9, i => 0);
    var lp := seq(9, i => 0);
    var ls := seq(9, i => 0);
    countCardsHelper(cards, 0, lm, lp, ls)
}

function countCardsHelper(cards: seq<string>, index: int, lm: seq<int>, lp: seq<int>, ls: seq<int>): (seq<int>, seq<int>, seq<int>)
    requires |lm| == 9 && |lp| == 9 && |ls| == 9
    requires 0 <= index <= |cards|
    ensures var result := countCardsHelper(cards, index, lm, lp, ls);
            |result.0| == 9 && |result.1| == 9 && |result.2| == 9
    decreases |cards| - index
{
    if index == |cards| then (lm, lp, ls)
    else if |cards[index]| >= 2 then
        var num := cards[index][0] as int - '0' as int;
        var suit := cards[index][1];
        if 1 <= num <= 9 then
            if suit == 'm' then
                countCardsHelper(cards, index + 1, lm[num-1 := lm[num-1] + 1], lp, ls)
            else if suit == 'p' then
                countCardsHelper(cards, index + 1, lm, lp[num-1 := lp[num-1] + 1], ls)
            else if suit == 's' then
                countCardsHelper(cards, index + 1, lm, lp, ls[num-1 := ls[num-1] + 1])
            else
                countCardsHelper(cards, index + 1, lm, lp, ls)
        else
            countCardsHelper(cards, index + 1, lm, lp, ls)
    else
        countCardsHelper(cards, index + 1, lm, lp, ls)
}

function seqCheckerFunc(arr: seq<int>): int
    requires |arr| == 9
{
    seqCheckerHelper(arr, 0, 0, 0)
}

function seqCheckerHelper(arr: seq<int>, index: int, currentSeq: int, maxSeq: int): int
    requires 0 <= index <= |arr|
    requires |arr| == 9
    decreases |arr| - index
{
    if index == |arr| then
        if currentSeq > maxSeq then currentSeq else maxSeq
    else if arr[index] == 1 then
        if currentSeq == 0 then
            seqCheckerHelper(arr, index + 1, 1, maxSeq)
        else
            seqCheckerHelper(arr, index + 1, currentSeq + 1, maxSeq)
    else
        var newMaxSeq := if currentSeq > maxSeq then currentSeq else maxSeq;
        seqCheckerHelper(arr, index + 1, 0, newMaxSeq)
}

function max3(a: int, b: int, c: int): int
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

function seqMax(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else
        var rest := seqMax(s[1..]);
        if s[0] > rest then s[0] else rest
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures ValidOutput(output)
    ensures CorrectResult(input, output)
// </vc-spec>
// <vc-code>
{
    if !ValidInput(input) {
        output := "2";
        return;
    }

    var cards := GetCards(input);
    var hasKoutsu := HasKoutsu(cards);
    var hasShuntsu := HasShuntsu(cards);

    if hasKoutsu || hasShuntsu {
        output := "0";
        return;
    }

    var hasPair := HasPair(cards);
    if hasPair {
        output := "1";
        return;
    }

    var bestWindow := GetBestWindow(cards);
    if bestWindow == 1 {
        output := "2";
    } else {
        output := "3";
    }
}
// </vc-code>

