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
lemma RepeatEveUnroll(count: int)
    requires count > 0
    ensures RepeatEve(count) == " Eve" + RepeatEve(count - 1)
{
    // This follows directly from the definition of RepeatEve
}

lemma RepeatEveAccumulate(count: int, acc: string)
    requires count >= 0
    ensures acc + RepeatEve(count) == 
            if count == 0 then acc 
            else RepeatEveAccumulate(count - 1, acc + " Eve")
    decreases count
{
    if count == 0 {
        // Base case: acc + RepeatEve(0) == acc + "" == acc
    } else {
        // Inductive case
        calc {
            acc + RepeatEve(count);
        == { RepeatEveUnroll(count); }
            acc + (" Eve" + RepeatEve(count - 1));
        == // String concatenation is associative
            (acc + " Eve") + RepeatEve(count - 1);
        == { RepeatEveAccumulate(count - 1, acc + " Eve"); }
            if count - 1 == 0 then acc + " Eve"
            else RepeatEveAccumulate(count - 2, (acc + " Eve") + " Eve");
        }
    }
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
// </vc-code>

