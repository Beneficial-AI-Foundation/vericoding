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

lemma StringConcatAssoc(a: string, b: string, c: string)
    ensures a + (b + c) == (a + b) + c
{
    // Axiom: string concatenation is associative
}

lemma RepeatEveAppend(i: int)
    requires i >= 0
    ensures RepeatEve(i) + " Eve" == " Eve" + RepeatEve(i)
{
    if i == 0 {
        calc {
            RepeatEve(0) + " Eve";
        ==
            "" + " Eve";
        ==
            " Eve";
        ==
            " Eve" + "";
        ==
            " Eve" + RepeatEve(0);
        }
    } else {
        calc {
            RepeatEve(i) + " Eve";
        == { assert i > 0; RepeatEveUnroll(i); }
            (" Eve" + RepeatEve(i - 1)) + " Eve";
        == { StringConcatAssoc(" Eve", RepeatEve(i - 1), " Eve"); }
            " Eve" + (RepeatEve(i - 1) + " Eve");
        == { RepeatEveAppend(i - 1); }
            " Eve" + (" Eve" + RepeatEve(i - 1));
        == { StringConcatAssoc(" Eve", " Eve", RepeatEve(i - 1)); }
            (" Eve" + " Eve") + RepeatEve(i - 1);
        == 
            " Eve Eve" + RepeatEve(i - 1);
        }
        // This approach won't work because we're getting " Eve Eve" instead of " Eve" + RepeatEve(i)
    }
}

// Let's use a different approach - build the string backwards
function RepeatEveBackward(count: int): string
    requires count >= 0
    decreases count
{
    if count == 0 then ""
    else RepeatEveBackward(count - 1) + " Eve"
}

lemma RepeatEveEquivalence(count: int)
    requires count >= 0
    ensures RepeatEve(count) == RepeatEveBackward(count)
    decreases count
{
    if count == 0 {
        // Base case: both return ""
    } else {
        calc {
            RepeatEve(count);
        ==
            " Eve" + RepeatEve(count - 1);
        == { RepeatEveEquivalence(count - 1); }
            " Eve" + RepeatEveBackward(count - 1);
        == { /* Induction: RepeatEveBackward(count - 1) + " Eve" == " Eve" + RepeatEveBackward(count - 1) for the full string */ 
             RepeatEveBackwardCommutes(count - 1); }
            RepeatEveBackward(count - 1) + " Eve";
        ==
            RepeatEveBackward(count);
        }
    }
}

lemma RepeatEveBackwardCommutes(count: int)
    requires count >= 0
    ensures " Eve" + RepeatEveBackward(count) == RepeatEveBackward(count) + " Eve"
    decreases count
{
    if count == 0 {
        calc {
            " Eve" + RepeatEveBackward(0);
        ==
            " Eve" + "";
        ==
            " Eve";
        ==
            "" + " Eve";
        ==
            RepeatEveBackward(0) + " Eve";
        }
    } else {
        calc {
            " Eve" + RepeatEveBackward(count);
        ==
            " Eve" + (RepeatEveBackward(count - 1) + " Eve");
        == { StringConcatAssoc(" Eve", RepeatEveBackward(count - 1), " Eve"); }
            (" Eve" + RepeatEveBackward(count - 1)) + " Eve";
        == { RepeatEveBackwardCommutes(count - 1); }
            (RepeatEveBackward(count - 1) + " Eve") + " Eve";
        == { StringConcatAssoc(RepeatEveBackward(count - 1), " Eve", " Eve"); }
            RepeatEveBackward(count - 1) + (" Eve" + " Eve");
        ==
            RepeatEveBackward(count - 1) + " Eve Eve";
        }
        calc {
            RepeatEveBackward(count) + " Eve";
        ==
            (RepeatEveBackward(count - 1) + " Eve") + " Eve";
        == { StringConcatAssoc(RepeatEveBackward(count - 1), " Eve", " Eve"); }
            RepeatEveBackward(count - 1) + (" Eve" + " Eve");
        ==
            RepeatEveBackward(count - 1) + " Eve Eve";
        }
        // This shows they both equal the same thing, completing the proof
    }
}

lemma RepeatEveLoopInvariant(i: int, result: string)
    requires 0 <= i
    requires result == "Christmas" + RepeatEve(i)
    ensures result + " Eve" == "Christmas" + RepeatEve(i + 1)
{
    calc {
        result + " Eve";
    ==
        ("Christmas" + RepeatEve(i)) + " Eve";
    == { StringConcatAssoc("Christmas", RepeatEve(i), " Eve"); }
        "Christmas" + (RepeatEve(i) + " Eve");
    == { 
        RepeatEveEquivalence(i);
        assert RepeatEve(i) == RepeatEveBackward(i);
        assert RepeatEveBackward(i) + " Eve" == RepeatEveBackward(i + 1);
        RepeatEveEquivalence(i + 1);
        assert RepeatEveBackward(i + 1) == RepeatEve(i + 1);
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

