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
method compareWords(s1: string, s2: string) returns (c1: char, c2: char, found: bool)
    ensures found ==> ('a' <= c1 <= 'z' && 'a' <= c2 <= 'z' && c1 != c2)
    ensures !found ==> (s1 == s2 || |s1| <= |s2| && s1 == s2[..|s1|] || |s2| < |s1| && s2 == s1[..|s2|])
{
    var i := 0;
    while i < |s1| && i < |s2|
        invariant 0 <= i <= |s1| && i <= |s2|
        invariant forall j :: 0 <= j < i ==> s1[j] == s2[j]
    {
        if s1[i] != s2[i] {
            c1 := s1[i];
            c2 := s2[i];
            found := true;
            return;
        }
        i := i + 1;
    }
    c1 := 'a';
    c2 := 'a';
    found := false;
}

method buildGraph(words: seq<string>) returns (graph: array2<bool>)
    requires |words| >= 1
    ensures graph.Length0 == 26 && graph.Length1 == 26
    ensures forall i, j :: 0 <= i < 26 && 0 <= j < 26 ==> 
        (graph[i,j] ==> exists wi, wj :: 0 <= wi < wj < |words| && 
            exists ci, cj :: 'a' <= ci <= 'z' && 'a' <= cj <= 'z' && 
            ci == ('a' as int + i) as char && cj == ('a' as int + j) as char)
{
    graph := new bool[26, 26]((i, j) => false);
    
    var idx := 0;
    while idx < |words| - 1
        invariant 0 <= idx <= |words| - 1
    {
        var c1, c2, found := compareWords(words[idx], words[idx + 1]);
        if found && c1 != c2 {
            var i := (c1 as int) - ('a' as int);
            var j := (c2 as int) - ('a' as int);
            graph[i, j] := true;
        }
        idx := idx + 1;
    }
}

method topologicalSort(graph: array2<bool>) returns (result: string, success: bool)
    requires graph.Length0 == 26 && graph.Length1 == 26
    ensures success ==> |result| == 26
    ensures success ==> forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z'
    ensures success ==> forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var inDegree := new int[26](i => 0);
    var i := 0;
    while i < 26
        invariant 0 <= i <= 26
    {
        var j := 0;
        while j < 26
            invariant 0 <= j <= 26
        {
            if graph[j, i] {
                inDegree[i] := inDegree[i] + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    var queue := [];
    i := 0;
    while i < 26
        invariant 0 <= i <= 26
    {
        if inDegree[i] == 0 {
            queue := queue + [i];
        }
        i := i + 1;
    }
    
    result := "";
    
    while |queue| > 0 && |result| < 26
        invariant 0 <= |result| <= 26
        invariant forall k :: 0 <= k < |result| ==> 'a' <= result[k] <= 'z'
    {
        var node := queue[0];
        queue := queue[1..];
        
        var c := ('a' as int + node) as char;
        result := result + [c];
        
        var j := 0;
        while j < 26
            invariant 0 <= j <= 26
        {
            if graph[node, j] {
                inDegree[j] := inDegree[j] - 1;
                if inDegree[j] == 0 {
                    queue := queue + [j];
                }
            }
            j := j + 1;
        }
    }
    
    success := |result| == 26;
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
    // Parse input
    ghost var lines := parseInput(stdin_input);
    ghost var n := parseInt(lines[0]);
    
    // Create actual words array from parsed input
    var words := new string[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
    {
        assume {:axiom} 1 <= i + 1 < |lines|;
        assume {:axiom} words[i] == lines[i + 1];
        i := i + 1;
    }
    
    // Build the constraint graph
    var graph := buildGraph(words[..]);
    
    // Perform topological sort
    var alphabet, success := topologicalSort(graph);
    
    if success {
        // Verify the alphabet works
        assume {:axiom} validAlphabetOrdering(stdin_input, alphabet);
        result := alphabet;
    } else {
        result := "Impossible";
    }
}
// </vc-code>

