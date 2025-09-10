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
lemma RepeatEveLemma(count: int, s: string)
    requires count >= 0
    ensures RepeatEve(count) == s <==> (count == 0 && s == "") || (count > 0 && s == " Eve" + RepeatEve(count - 1))
{
}

lemma ExpectedOutputLemma(d: int)
    requires ValidInput(d)
    ensures ExpectedOutput(d) == (if 25 - d == 0 then "Christmas" else "Christmas" + RepeatEve(25 - d))
{
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
    if eveCount == 0 {
        result := "Christmas";
    } else {
        result := "Christmas";
        var i := 0;
        while i < eveCount
            invariant 0 <= i <= eveCount
            invariant result == "Christmas" + RepeatEve(i)
        {
            result := result + " Eve";
            i := i + 1;
        }
    }
}
// </vc-code>

