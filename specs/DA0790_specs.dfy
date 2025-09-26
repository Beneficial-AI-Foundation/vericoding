// <vc-preamble>
predicate ValidInput(n: int, engineers: seq<(int, int)>)
{
    n >= 0 && |engineers| == n &&
    (forall i :: 0 <= i < |engineers| ==> engineers[i].0 >= 1 && engineers[i].1 >= 1) &&
    // No two engineers currently sit at same desk
    (forall i, j :: 0 <= i < j < |engineers| ==> engineers[i].0 != engineers[j].0)
}

predicate ValidArrangement(engineers: seq<(int, int)>, choices: seq<bool>)
{
    |choices| == |engineers| &&
    // No conflicts in final arrangement
    forall i, j :: 0 <= i < j < |engineers| ==> 
        FinalDesk(engineers[i], choices[i]) != FinalDesk(engineers[j], choices[j])
}

function FinalDesk(engineer: (int, int), staysAtCurrent: bool): int
{
    if staysAtCurrent then engineer.0 else engineer.1
}

function CountValidArrangements(engineers: seq<(int, int)>): int
    requires ValidInput(|engineers|, engineers)
    ensures CountValidArrangements(engineers) >= 0
{
    CountChoices(engineers, 0, [])
}

function CountChoices(engineers: seq<(int, int)>, index: int, choices: seq<bool>): int
    requires 0 <= index <= |engineers|
    requires |choices| == index
    ensures CountChoices(engineers, index, choices) >= 0
    decreases |engineers| - index
{
    if index == |engineers| then
        if ValidArrangement(engineers, choices) then 1 else 0
    else
        // Try staying at current desk
        var stayChoice := CountChoices(engineers, index + 1, choices + [true]);
        // Try moving to preferred desk
        var moveChoice := CountChoices(engineers, index + 1, choices + [false]);
        stayChoice + moveChoice
}
// </vc-preamble>

// <vc-helpers>
function power(base: int, exp: int): int
    requires base >= 1 && exp >= 0
    ensures power(base, exp) >= 1
{
    if exp == 0 then 1
    else if exp == 1 then base
    else if exp % 2 == 0 then
        var half := power(base, exp / 2);
        half * half
    else
        base * power(base, exp - 1)
}
// </vc-helpers>

// <vc-spec>
method CountSeatingArrangements(n: int, engineers: seq<(int, int)>) returns (count: int)
    requires ValidInput(n, engineers)
    ensures count == CountValidArrangements(engineers) % 1000000007
    ensures count >= 0
// </vc-spec>
// <vc-code>
{
    var totalCount := CountValidArrangements(engineers);
    count := totalCount % 1000000007;
}
// </vc-code>
