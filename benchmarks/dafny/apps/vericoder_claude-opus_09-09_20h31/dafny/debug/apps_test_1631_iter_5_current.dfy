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
ghost function indexOf(c: char, alphabet: string): int
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
    requires 'a' <= c <= 'z'
    ensures 0 <= indexOf(c, alphabet) < |alphabet|
    ensures alphabet[indexOf(c, alphabet)] == c
{
    var i :| 0 <= i < |alphabet| && alphabet[i] == c;
    i
}

lemma LexOrderTransitive(s1: string, s2: string, s3: string, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
    requires lexicographicallyLessOrEqual(s1, s2, alphabet)
    requires lexicographicallyLessOrEqual(s2, s3, alphabet)
    ensures lexicographicallyLessOrEqual(s1, s3, alphabet)
{
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
    
    // Build adjacency list for character precedence graph
    var graph := map[];
    var inDegree := map[];
    var allChars := {};
    
    // Initialize for all lowercase letters
    var c := 'a';
    while c <= 'z'
        invariant 'a' <= c <= ('z' as char + 1 as char)
    {
        graph := graph[c := {}];
        inDegree := inDegree[c := 0];
        allChars := allChars + {c};
        c := (c as int + 1) as char;
    }
    
    // Build graph from consecutive word pairs
    var i := 1;
    while i < n
        invariant 1 <= i <= n
    {
        var word1 := lines[i];
        var word2 := lines[i + 1];
        
        // Find first differing character
        var j := 0;
        var minLen := if |word1| < |word2| then |word1| else |word2|;
        
        while j < minLen && word1[j] == word2[j]
            invariant 0 <= j <= minLen
        {
            j := j + 1;
        }
        
        if j < minLen {
            // word1[j] must come before word2[j]
            var c1 := word1[j];
            var c2 := word2[j];
            
            // Add edge if it doesn't already exist
            if c2 !in graph[c1] {
                graph := graph[c1 := graph[c1] + {c2}];
                inDegree := inDegree[c2 := inDegree[c2] + 1];
            }
        } else if |word1| > |word2| {
            // Invalid: longer word comes before its prefix
            return "Impossible";
        }
        
        i := i + 1;
    }
    
    // Topological sort using Kahn's algorithm
    var queue := [];
    c := 'a';
    while c <= 'z'
        invariant 'a' <= c <= ('z' as char + 1 as char)
    {
        if inDegree[c] == 0 {
            queue := queue + [c];
        }
        c := (c as int + 1) as char;
    }
    
    var alphabetOrder := "";
    
    while |queue| > 0
        invariant |alphabetOrder| <= 26
        invariant forall k :: 0 <= k < |alphabetOrder| ==> 'a' <= alphabetOrder[k] <= 'z'
    {
        var curr := queue[0];
        queue := queue[1..];
        alphabetOrder := alphabetOrder + [curr];
        
        // Process neighbors
        if curr in graph {
            var neighbors := graph[curr];
            var neighborList := [];
            
            // Convert set to sequence for iteration
            c := 'a';
            while c <= 'z'
                invariant 'a' <= c <= ('z' as char + 1 as char)
            {
                if c in neighbors {
                    neighborList := neighborList + [c];
                }
                c := (c as int + 1) as char;
            }
            
            var k := 0;
            while k < |neighborList|
                invariant 0 <= k <= |neighborList|
            {
                var neighbor := neighborList[k];
                inDegree := inDegree[neighbor := inDegree[neighbor] - 1];
                if inDegree[neighbor] == 0 {
                    queue := queue + [neighbor];
                }
                k := k + 1;
            }
        }
    }
    
    if |alphabetOrder| != 26 {
        result := "Impossible";
    } else {
        result := alphabetOrder;
    }
}
// </vc-code>

