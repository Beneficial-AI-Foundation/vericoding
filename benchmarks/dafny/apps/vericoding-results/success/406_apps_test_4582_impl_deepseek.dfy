predicate ValidInput(input: string)
{
    |input| >= 3 &&
    input[1] == ' ' &&
    input[0] in {'H', 'D'} &&
    input[2] in {'H', 'D'} &&
    (|input| == 3 || (|input| > 3 && input[3] == '\n'))
}

function CorrectOutput(input: string): string
    requires ValidInput(input)
{
    if (input[0] == 'H' && input[2] == 'H') || (input[0] == 'D' && input[2] == 'D')
    then "H\n"
    else "D\n"
}

// <vc-helpers>
lemma InputProperties(input: string)
    requires ValidInput(input)
    ensures (input[0] == 'H' && input[2] == 'H') || (input[0] == 'H' && input[2] == 'D') ||
            (input[0] == 'D' && input[2] == 'H') || (input[0] == 'D' && input[2] == 'D')
{
}

lemma CorrectOutputProperties(input: string)
    requires ValidInput(input)
    ensures if (input[0] == 'H' && input[2] == 'H') || (input[0] == 'D' && input[2] == 'D')
            then CorrectOutput(input) == "H\n"
            else CorrectOutput(input) == "D\n"
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == CorrectOutput(input)
    ensures result == "H\n" || result == "D\n"
// </vc-spec>
// <vc-code>
{
    InputProperties(input);
    CorrectOutputProperties(input);
    if (input[0] == 'H' && input[2] == 'H') || (input[0] == 'D' && input[2] == 'D') {
        result := "H\n";
    } else {
        result := "D\n";
    }
}
// </vc-code>

