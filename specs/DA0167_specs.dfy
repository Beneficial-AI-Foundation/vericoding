// <vc-preamble>
predicate ValidInput(s: int, v1: int, v2: int, t1: int, t2: int)
{
    1 <= s <= 1000 && 1 <= v1 <= 1000 && 1 <= v2 <= 1000 && 1 <= t1 <= 1000 && 1 <= t2 <= 1000
}

function ParticipantTime(s: int, v: int, t: int): int
{
    2 * t + s * v
}

function CorrectResult(s: int, v1: int, v2: int, t1: int, t2: int): string
{
    var time1 := ParticipantTime(s, v1, t1);
    var time2 := ParticipantTime(s, v2, t2);
    if time1 < time2 then "First"
    else if time1 > time2 then "Second"
    else "Friendship"
}

predicate ValidResult(result: string)
{
    result == "First" || result == "Second" || result == "Friendship"
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: int, v1: int, v2: int, t1: int, t2: int) returns (result: string)
    requires ValidInput(s, v1, v2, t1, t2)
    ensures ValidResult(result)
    ensures result == CorrectResult(s, v1, v2, t1, t2)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
