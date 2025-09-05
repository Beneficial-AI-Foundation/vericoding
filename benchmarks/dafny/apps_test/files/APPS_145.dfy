This verification task involves implementing a gender determination algorithm based on the number of distinct characters in a username. Given a username of lowercase English letters, the algorithm determines gender by counting distinct characters: if the count is odd, output "IGNORE HIM!" (male), and if even, output "CHAT WITH HER!" (female).

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

// ======= HELPERS =======

// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures output == "IGNORE HIM!" || output == "CHAT WITH HER!"
    ensures CorrectOutput(input, output)
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

    if |distinctChars| % 2 == 1 {
        output := "IGNORE HIM!";
    } else {
        output := "CHAT WITH HER!";
    }
}
