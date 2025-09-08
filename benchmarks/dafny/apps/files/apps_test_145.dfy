Given a username string containing only lowercase English letters, determine the user's gender
based on the number of distinct characters: odd count means male, even count means female.
Output "IGNORE HIM!" for male, "CHAT WITH HER!" for female.

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

method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures var username := input[..|input|-1];
            CorrectOutput(username, output)
{
    var username := input[..|input|-1];
    var chars := {};
    var i := 0;
    while i < |username|
        invariant 0 <= i <= |username|
        invariant chars == set c | 0 <= c < i :: username[c]
    {
        chars := chars + {username[i]};
        i := i + 1;
    }

    if |chars| % 2 == 1 {
        output := "IGNORE HIM!\n";
    } else {
        output := "CHAT WITH HER!\n";
    }
}
