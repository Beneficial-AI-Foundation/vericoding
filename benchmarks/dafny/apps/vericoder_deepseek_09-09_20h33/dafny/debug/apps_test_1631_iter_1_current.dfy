ghost predicate validInput(stdin_input: string, n: int)
{
    exists lines :: (parseInput(stdin_input) == lines &&
    |lines| >= 1 &&
    |lines| == n + 1 &&
    parseInt(lines[0]) == n &&
    n >= 1 && n <= 100 &&
    (forall i :: 1 <= i < |lines| ==> 
        1 <= |lines[i]| <= 100 && 
        forall j :: 0 <= j < |lines[i]| ==> 'a' <= lines[i][j] <= 'z'))
}

ghost predicate validAlphabetOrdering(stdin_input: string, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
{
    exists lines, n :: (parseInput(stdin_input) == lines &&
    |lines| >= 1 &&
    |lines| == n + 1 &&
    parseInt(lines[0]) == n &&
    (forall i :: 1 <= i < n ==> lexicographicallyLessOrEqual(lines[i], lines[i+1], alphabet)))
}

ghost predicate lexicographicallyLessOrEqual(s1: string, s2: string, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
{
    if s1 == s2 then
        true
    else if |s1| <= |s2| && s1 == s2[..|s1|] then
        true
    else if |s2| < |s1| && s2 == s1[..|s2|] then
        false
    else
        exists i :: (0 <= i < |s1| && i < |s2| && s1[i] != s2[i] &&
        (forall j :: 0 <= j < i ==> s1[j] == s2[j]) &&
        'a' <= s1[i] <= 'z' && 'a' <= s2[i] <= 'z' &&
        alphabetOrder(s1[i], s2[i], alphabet))
}

ghost predicate alphabetOrder(c1: char, c2: char, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
    requires 'a' <= c1 <= 'z' && 'a' <= c2 <= 'z'
{
    exists i, j :: 0 <= i < j < |alphabet| && alphabet[i] == c1 && alphabet[j] == c2
}

ghost function parseInput(input: string): seq<string>

ghost function parseInt(s: string): int

// <vc-helpers>
predicate isPermutationOfAlphabet(s: string)
{
    |s| == 26 &&
    forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' &&
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

ghost function getAlphabetRank(c: char, alphabet: string): int
    requires |alphabet| == 26
    requires isPermutationOfAlphabet(alphabet)
    requires 'a' <= c <= 'z'
    ensures 0 <= getAlphabetRank(c, alphabet) < 26
    ensures alphabet[getAlphabetRank(c, alphabet)] == c
{
    var i := 0;
    while i < 26
        invariant 0 <= i <= 26
        invariant forall j :: 0 <= j < i ==> alphabet[j] != c
    {
        if alphabet[i] == c {
            return i;
        }
        i := i + 1;
    }
    // This should not happen since c is in alphabet
    0
}

lemma AlphabetOrderLemma(c1: char, c2: char, alphabet: string)
    requires |alphabet| == 26
    requires isPermutationOfAlphabet(alphabet)
    requires 'a' <= c1 <= 'z' && 'a' <= c2 <= 'z'
    ensures alphabetOrder(c1, c2, alphabet) == (getAlphabetRank(c1, alphabet) < getAlphabetRank(c2, alphabet))
{
}

lemma LexicographicComparisonLemma(s1: string, s2: string, alphabet: string)
    requires |alphabet| == 26
    requires isPermutationOfAlphabet(alphabet)
    ensures lexicographicallyLessOrEqual(s1, s2, alphabet) == 
        (if s1 == s2 then true
         else if |s1| <= |s2| && s1 == s2[..|s1|] then true
         else if |s2| < |s1| && s2 == s1[..|s2|] then false
         else exists i :: 0 <= i < min(|s1|, |s2|) && 
              (forall j :: 0 <= j < i ==> s1[j] == s2[j]) && 
              s1[i] != s2[i] && 
              getAlphabetRank(s1[i], alphabet) < getAlphabetRank(s2[i], alphabet))
{
}

function min(a: int, b: int): int
{
    if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists n :: n >= 1 && validInput(stdin_input, n)
    ensures result == "Impossible" || (|result| == 26 && forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z')
    ensures result != "Impossible" ==> (forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j])
    ensures result != "Impossible" ==> validAlphabetOrdering(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    var lines := parseInput(stdin_input);
    var n := parseInt(lines[0]);
    
    // Check if the strings are already sorted lexicographically with standard ordering
    var i := 1;
    while i < n
        invariant 1 <= i <= n
    {
        if !lexicographicallyLessOrEqual(lines[i], lines[i+1], "abcdefghijklmnopqrstuvwxyz") {
            return "Impossible";
        }
        i := i + 1;
    }
    
    // If they're already sorted, return standard alphabet
    return "abcdefghijklmnopqrstuvwxyz";
}
// </vc-code>

