// ======= TASK =======
// Given a username of lowercase English letters, determine gender based on the number of distinct characters.
// If the count is odd, output "IGNORE HIM!" (male). If even, output "CHAT WITH HER!" (female).

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(input: string)
{
    |input| > 0 && forall i :: 0 <= i < |input| ==> 'a' <= input[i] <= 'z' || input[i] == '\n'
}

function CleanUsername(input: string): string
    requires ValidInput(input)
{
    if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input
}

function DistinctChars(username: string): set<char>
{
    set i | 0 <= i < |username| :: username[i]
}

predicate CorrectOutput(input: string, output: string)
    requires ValidInput(input)
{
    var username := CleanUsername(input);
    var distinctChars := DistinctChars(username);
    (|distinctChars| % 2 == 1 ==> output == "IGNORE HIM!") &&
    (|distinctChars| % 2 == 0 ==> output == "CHAT WITH HER!")
}

// <vc-helpers>
lemma DistinctCharsEquivalence(username: string, i: int, distinctChars: set<char>)
    requires 0 <= i <= |username|
    requires distinctChars == set j | 0 <= j < i :: username[j]
    ensures distinctChars == DistinctChars(username[..i])
{
    assert username[..i] == username[0..i];
    var expected := DistinctChars(username[..i]);
    assert expected == set k | 0 <= k < |username[..i]| :: username[..i][k];
    assert expected == set k | 0 <= k < i :: username[k];
}

lemma DistinctCharsComplete(username: string)
    ensures DistinctChars(username) == set j | 0 <= j < |username| :: username[j]
{
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures output == "IGNORE HIM!" || output == "CHAT WITH HER!"
    ensures CorrectOutput(input, output)
// </vc-spec>
// <vc-code>
{
    var username := CleanUsername(input);
    
    var distinctChars := {};
    var i := 0;
    while i < |username|
        invariant 0 <= i <= |username|
        invariant distinctChars == set j | 0 <= j < i :: username[j]
    {
        distinctChars := distinctChars + {username[i]};
        i := i + 1;
    }

    assert distinctChars == DistinctChars(username);

    if |distinctChars| % 2 == 1 {
        output := "IGNORE HIM!";
    } else {
        output := "CHAT WITH HER!";
    }
}
// </vc-code>

