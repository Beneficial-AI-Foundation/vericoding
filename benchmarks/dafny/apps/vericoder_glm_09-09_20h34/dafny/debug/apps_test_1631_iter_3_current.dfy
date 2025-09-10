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
ghost function indexOf(str: string, c: char): int
    requires 'a' <= c <= 'z'
    requires exists i :: 0 <= i < |str| && str[i] == c
    ensures 0 <= indexOf(str, c) < |str| && str[indexOf(str, c)] == c
{
    if str[0] == c then 0 else indexOf(str[1:], c) + 1
}

ghost function charLessThan(c1: char, c2: char, alphabet: string): bool
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
    requires 'a' <= c1 <= 'z' && 'a' <= c2 <= 'z'
    ensures charLessThan(c1, c2, alphabet) ==> indexOf(alphabet, c1) < indexOf(alphabet, c2)
{
    indexOf(alphabet, c1) < indexOf(alphabet, c2)
}

ghost method constructOrdering(lines: seq<string>) returns (alphabet: string)
    requires |lines| >= 2
    requires forall i :: 0 <= i < |lines| ==> 1 <= |lines[i]| <= 100
    requires forall i :: 0 <= i < |lines| ==> forall j :: 0 <= j < |lines[i]| ==> 'a' <= lines[i][j] <= 'z'
    ensures |alphabet| == 26
    ensures forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    ensures forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
{
    var graph := new char[26];
    var inDegree := new int[26];
    var chars := new bool[26];
    var numChars := 0;
    
    // Initialize arrays
    var i := 0;
    while i < 26
        invariant 0 <= i <= 26
        invariant forall j :: 0 <= j < i ==> chars[j] == false
        invariant forall j :: 0 <= j < i ==> inDegree[j] == 0
    {
        chars[i] := false;
        inDegree[i] := 0;
        i := i + 1;
    }
    
    // Find all characters in the input
    i := 0;
    while i < |lines|
        invariant 0 <= i <= |lines|
        invariant forall j :: 0 <= j < 26 ==> chars[j] ==> exists k :: 0 <= k < i && exists l :: 0 <= l < |lines[k]| && lines[k][l] == 'a' + j
    {
        var j := 0;
        while j < |lines[i]|
            invariant 0 <= j <= |lines[i]|
            invariant forall k :: 0 <= k < 26 ==> chars[k] ==> 
                (exists l :: 0 <= l < i && exists m :: 0 <= m < |lines[l]| && lines[l][m] == 'a' + k) ||
                (l == i && exists n :: 0 <= n < j && lines[i][n] == 'a' + k)
        {
            var c := lines[i][j];
            var idx := c - 'a';
            if !chars[idx] {
                chars[idx] := true;
                numChars := numChars + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Build constraints from adjacent words
    i := 0;
    while i < |lines| - 1
        invariant 0 <= i <= |lines| - 1
        invariant forall j :: 0 <= j < 26 ==> forall k :: 0 <= k < 26 ==>
            (graph[j] == 'a' + k) ==> (exists l :: 0 <= l < i && 
                lexicographicallyLessOrEqual(lines[l], lines[l+1], ""))
    {
        var word1 := lines[i];
        var word2 := lines[i+1];
        var j := 0;
        var found := false;
        while j < |word1| && j < |word2| && !found
            invariant 0 <= j <= |word1| && j <= |word2|
            invariant !found ==> forall k :: 0 <= k < j ==> word1[k] == word2[k]
        {
            if word1[j] != word2[j] {
                var c1 := word1[j];
                var c2 := word2[j];
                var idx1 := c1 - 'a';
                var idx2 := c2 - 'a';
                graph[idx1] := c2;
                inDegree[idx2] := inDegree[idx2] + 1;
                found := true;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Topological sort to build alphabet
    alphabet := "";
    var q := new char[26];
    var head := 0;
    var tail := 0;
    
    i := 0;
    while i < 26
        invariant 0 <= i <= 26
        invariant forall j :: 0 <= j < 26 ==> inDegree[j] == 0 ==> j < i
        invariant forall j :: 0 <= j < head ==> inDegree[q[j] - 'a'] == 0
    {
        if chars[i] && inDegree[i] == 0 {
            q[tail] := 'a' + i;
            tail := tail + 1;
        }
        i := i + 1;
    }
    
    while head < tail
        invariant 0 <= head <= tail <= 26
        invariant |alphabet| == head
        invariant forall j :: 0 <= j < |alphabet| ==> 'a' <= alphabet[j] <= 'z'
        invariant forall j, k :: 0 <= j < k < |alphabet| ==> alphabet[j] != alphabet[k]
    {
        var u := q[head];
        head := head + 1;
        alphabet := alphabet + u;
        var idx := u - 'a';
        if chars[idx] && graph[idx] != '\0' {
            var v := graph[idx];
            var vidx := v - 'a';
            inDegree[vidx] := inDegree[vidx] - 1;
            if inDegree[vidx] == 0 {
                q[tail] := v;
                tail := tail + 1;
            }
        }
    }
    
    if |alphabet| != numChars {
        alphabet := "Impossible";
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
  var words := lines[1..];
  var result := constructOrdering(words);
  if result == "Impossible" {
    return "Impossible";
  }
  return result;
}
// </vc-code>

