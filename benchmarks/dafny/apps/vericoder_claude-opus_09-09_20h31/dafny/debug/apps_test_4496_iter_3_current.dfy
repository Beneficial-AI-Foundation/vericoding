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

lemma RepeatEveAddOne(i: int)
    requires i >= 0
    ensures RepeatEve(i + 1) == " Eve" + RepeatEve(i)
{
    // By definition of RepeatEve:
    // RepeatEve(i + 1) = if (i + 1) == 0 then "" else " Eve" + RepeatEve((i + 1) - 1)
    // Since i >= 0, we have i + 1 > 0, so:
    // RepeatEve(i + 1) = " Eve" + RepeatEve(i)
}

lemma RepeatEveLoopInvariant(i: int, result: string)
    requires 0 <= i
    requires result == "Christmas" + RepeatEve(i)
    ensures result + " Eve" == "Christmas" + RepeatEve(i + 1)
{
    calc {
        result + " Eve";
    ==
        "Christmas" + RepeatEve(i) + " Eve";
    == // By associativity of string concatenation
        "Christmas" + (RepeatEve(i) + " Eve");
    == { 
        // We need to show RepeatEve(i) + " Eve" == " Eve" + RepeatEve(i)
        // This is true by commutativity for single " Eve" additions
        assert RepeatEve(i + 1) == " Eve" + RepeatEve(i) by {
            RepeatEveAddOne(i);
        }
        // But we have RepeatEve(i) + " Eve", which needs rearrangement
        // Actually, let's use the fact that RepeatEve builds from the left
        calc {
            " Eve" + RepeatEve(i);
        == { RepeatEveAddOne(i); }
            RepeatEve(i + 1);
        }
    }
        "Christmas" + RepeatEve(i + 1);
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
        RepeatEveLoopInvariant(i, result);
        result := result + " Eve";
        i := i + 1;
    }
}
// </vc-code>

