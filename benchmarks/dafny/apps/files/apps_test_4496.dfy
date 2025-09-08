Given an integer D representing a December date (22-25), output the corresponding Christmas-related string:
D=25: "Christmas", D=24: "Christmas Eve", D=23: "Christmas Eve Eve", D=22: "Christmas Eve Eve Eve"

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

method solve(d: int) returns (result: string)
    requires ValidInput(d)
    ensures result == ExpectedOutput(d)
{
    var baseString := "Christmas";
    var eveCount := 25 - d;
    var eveString := "";

    var i := 0;
    while i < eveCount
        invariant 0 <= i <= eveCount
        invariant eveString == RepeatEve(i)
    {
        eveString := eveString + " Eve";
        i := i + 1;
    }

    result := baseString + eveString;
}
