predicate ValidInput(d: int) {
    22 <= d <= 25
}

function ExpectedOutput(d: int): string
    requires ValidInput(d)
{
    var eveCount := 25 - d;
    var baseString := "Christmas";
    if eveCount == 0 then baseString
    else baseString + RepeatEve(eveCount)
}

function RepeatEve(count: int): string
    requires count >= 0
    decreases count
{
    if count == 0 then ""
    else " Eve" + RepeatEve(count - 1)
}

// <vc-helpers>
function RepeatEve(count: int): string
    requires count >= 0
    decreases count
{
    if count == 0 then ""
    else " Eve" + RepeatEve(count - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(d: int) returns (result: string)
    requires ValidInput(d)
    ensures result == ExpectedOutput(d)
// </vc-spec>
// <vc-code>
{
    var eveCount := 25 - d;
    var baseString := "Christmas";
    if eveCount == 0 then
        result := baseString;
    else
        var s := "";
        var i := 0;
        while i < eveCount
            invariant 0 <= i <= eveCount
            invariant s == RepeatEve(i)
            decreases eveCount - i
        {
            s := s + " Eve";
            i := i + 1;
        }
        result := baseString + s;
}
// </vc-code>

