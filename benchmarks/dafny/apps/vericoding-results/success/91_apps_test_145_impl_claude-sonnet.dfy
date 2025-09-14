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
lemma CountDistinctCorrect(s: string)
    ensures CountDistinct(s) == |set c | 0 <= c < |s| :: s[c]|
{
    // This lemma is automatically proven by Dafny
}

lemma SetCardinalityParity(s: string)
    ensures var chars := set c | 0 <= c < |s| :: s[c];
            (|chars| % 2 == 1) <==> (CountDistinct(s) % 2 == 1)
{
    // This follows from the definition of CountDistinct
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
    var distinctChars := set c | 0 <= c < |username| :: username[c];
    var distinctCount := |distinctChars|;
    
    if distinctCount % 2 == 1 {
        output := "IGNORE HIM!\n";
    } else {
        output := "CHAT WITH HER!\n";
    }
}
// </vc-code>

