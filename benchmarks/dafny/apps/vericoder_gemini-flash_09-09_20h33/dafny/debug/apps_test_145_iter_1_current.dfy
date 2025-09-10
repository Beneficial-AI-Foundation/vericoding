function CountDistinct(s: string): int
{
    |set c | 0 <= c < |s| :: s[c]|
}

predicate ValidInput(input: string)
{
    |input| > 0 &&
    input[|input|-1] == '\n' &&
    |input| >= 2 &&
    forall i :: 0 <= i < |input|-1 ==> 'a' <= input[i] <= 'z'
}

predicate CorrectOutput(username: string, output: string)
{
    var distinctCount := CountDistinct(username);
    (distinctCount % 2 == 1 ==> output == "IGNORE HIM!\n") &&
    (distinctCount % 2 == 0 ==> output == "CHAT WITH HER!\n")
}

// <vc-helpers>
function CountDistinctChar(s: string): (count: int)
    ensures count == |set c | 0 <= c < |s| :: s[c]|
{
    if |s| == 0 then
        0
    else
        var char_set := set s[0];
        var i := 1;
        while i < |s|
            invariant 0 < i <= |s|
            invariant char_set == set x | 0 <= x < i :: s[x]
        {
            char_set := char_set + {s[i]};
            i := i + 1;
        }
        |char_set|
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures var username := input[..|input|-1];
            CorrectOutput(username, output)
// </vc-spec>
// <vc-code>
{
    var username := input[..|input|-1];
    var distinctCount := CountDistinctChar(username);
    if distinctCount % 2 == 1 {
        output := "IGNORE HIM!\n";
    } else {
        output := "CHAT WITH HER!\n";
    }
}
// </vc-code>

