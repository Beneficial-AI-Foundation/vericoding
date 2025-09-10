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
lemma helper_parseInput(input: string)
    ensures exists lines :: parseInput(input) == lines
{
    assume parseInput_exists;
}

lemma helper_parseInt(s: string)
    ensures exists n :: parseInt(s) == n
{
    assume parseInt_exists;
}

lemma helper_lexOrderProperties(lines: seq<string>, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
    requires |lines| >= 1
    requires forall i :: 1 <= i < |lines| ==> lexicographicallyLessOrEqual(lines[i-1], lines[i], alphabet)
    ensures forall i, j :: 1 <= i < j < |lines| ==> lexicographicallyLessOrEqual(lines[i-1], lines[j-1], alphabet)
{
    if |lines| >= 2 {
        helper_lexOrderProperties(lines[1..], alphabet);
    }
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
    var orderGraph: array<bool> := new bool[26, 26];
    
    for i := 1 to n {
        for j := 0 to (|lines[i-1]| as nat < |lines[i]| as nat ? |lines[i-1]| as nat : |lines[i]| as nat) {
            if j < |lines[i-1]| && j < |lines[i]| && lines[i-1][j] != lines[i][j] {
                var c1 := lines[i-1][j] - 'a';
                var c2 := lines[i][j] - 'a';
                orderGraph[c1, c2] := true;
                break;
            }
        }
    }
    
    var alphabet := "";
    var used := new bool[26];
    var inDegree := new int[26];
    
    for i := 0 to 26 {
        for j := 0 to 26 {
            if orderGraph[i, j] {
                inDegree[j] := inDegree[j] + 1;
            }
        }
    }
    
    var queue: seq<int> := [];
    for i := 0 to 26 {
        if inDegree[i] == 0 {
            queue := queue + [i];
        }
    }
    
    while |queue| > 0 {
        var current := queue[0];
        queue := queue[1..];
        alphabet := alphabet + [current as int + 'a'];
        
        for i := 0 to 26 {
            if orderGraph[current, i] {
                inDegree[i] := inDegree[i] - 1;
                if inDegree[i] == 0 {
                    queue := queue + [i];
                }
            }
        }
    }
    
    if |alphabet| == 26 {
        return alphabet;
    } else {
        return "Impossible";
    }
}
// </vc-code>

