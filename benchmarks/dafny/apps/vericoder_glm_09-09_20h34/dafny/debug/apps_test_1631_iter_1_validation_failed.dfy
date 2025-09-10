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
ghost method findIndex(c: char, alphabet: string) returns (index: int)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
    requires 'a' <= c <= 'z'
    ensures 0 <= index < 26
    ensures alphabet[index] == c
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
    // Should not reach here due to precondition on alphabet
    return 0;
}

ghost method lexCompare(s1: string, s2: string, alphabet: string) returns (cmp: int)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
    ensures cmp == 0 || cmp == -1 || cmp == 1
    ensures (cmp == 0) <==> (s1 == s2)
    ensures (cmp == -1) <==> lexicographicallyLessOrEqual(s1, s2, alphabet) && s1 != s2
    ensures (cmp == 1) <==> !lexicographicallyLessOrEqual(s1, s2, alphabet) && s1 != s2
{
    if s1 == s2 {
        return 0;
    }
    var len := if |s1| < |s2| then |s1| else |s2|;
    var i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant forall j :: 0 <= j < i ==> s1[j] == s2[j]
    {
        if s1[i] != s2[i] {
            var idx1 := findIndex(s1[i], alphabet);
            var idx2 := findIndex(s2[i], alphabet);
            if idx1 < idx2 {
                return -1;
            } else {
                return 1;
            }
        }
        i := i + 1;
    }
    // Common prefix is the whole shorter string
    if |s1| < |s2| {
        return -1;
    } else {
        return 1;
    }
}

predicate allCharsInAlphabet(lines: seq<string>, alphabet: string)
    requires |alphabet| == 26
    requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
{
    forall i :: 0 <= i < |lines| ==> 
        forall j :: 0 <= j < |lines[i]| ==> 
            exists k :: 0 <= k < |alphabet| && alphabet[k] == lines[i][j]
}

ghost function generateAlphabet(order: seq<char>): string
    requires |order| == 26
    requires forall i :: 0 <= i < |order| ==> 'a' <= order[i] <= 'z'
    requires forall i, j :: 0 <= i < j < |order| ==> order[i] != order[j]
{
    var s := "";
    var i := 0;
    while i < 26
        invariant 0 <= i <= 26
        invariant |s| == i
        invariant forall j :: 0 <= j < i ==> s[j] == order[j]
    {
        s := s + [order[i]];
        i := i + 1;
    }
    s
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
    
    // Collect all unique characters from the input
    var unique_chars := new set<char>;
    var all_unique_chars := new set<char>;
    var i := 1;
    while i < |lines|
        invariant 1 <= i <= |lines|
        invariant forall c :: c in unique_chars ==> (exists k :: 1 <= k < i && c in lines[k][..])
    {
        var j := 0;
        while j < |lines[i]|
            invariant 0 <= j <= |lines[i]|
            invariant forall c :: c in unique_chars ==> (exists k :: 1 <= k < i && c in lines[k][..]) || c in lines[i][..j]
        {
            unique_chars := unique_chars + {lines[i][j]};
            all_unique_chars := all_unique_chars + {lines[i][j]};
            j := j + 1;
        }
        i := i + 1;
    }

    // If there are more than 26 unique characters, it's impossible
    if |unique_chars| > 26 {
        return "Impossible";
    }

    // Initialize a directed graph representing character ordering constraints
    var graph := new map<char, set<char>>;
    var chars := unique_chars.Keys;
    var c1_idx := 0;
    while c1_idx < |chars|
        invariant 0 <= c1_idx <= |chars|
    {
        graph[chars[c1_idx]] := new set<char>;
        c1_idx := c1_idx + 1;
    }

    // Build the graph by comparing consecutive words
    var word_idx := 1;
    while word_idx < n // lines[word_idx] and lines[word_idx+1]
        invariant 1 <= word_idx <= n
    {
        var s1 := lines[word_idx];
        var s2 := lines[word_idx + 1];
        var len := if |s1| < |s2| then |s1| else |s2|;
        var found_first_diff := false;
        var char_idx := 0;
        while char_idx < len && !found_first_diff
            invariant 0 <= char_idx <= len
            invariant found_first_diff ==> (exists k :: 0 <= k < char_idx && s1[k] != s2[k])
        {
            if s1[char_idx] != s2[char_idx] {
                // s1[char_idx] must come before s2[char_idx] in the alphabet
                graph[s1[char_idx]] := graph[s1[char_idx]] + {s2[char_idx]};
                found_first_diff := true;
            }
            char_idx := char_idx + 1;
        }
        // If one word is a prefix of the other, the shorter one must come first
        if !found_first_diff && |s1| > |s2| {
            return "Impossible";
        }
        word_idx := word_idx + 1;
    }

    // Perform topological sort
    var in_degree := new map<char, int>;
    c1_idx := 0;
    while c1_idx < |chars|
        invariant 0 <= c1_idx <= |chars|
    {
        in_degree[chars[c1_idx]] := 0;
        c1_idx := c1_idx + 1;
    }

    // Calculate in-degrees for all nodes
    c1_idx := 0;
    while c1_idx < |chars|
        invariant 0 <= c1_idx <= |chars|
    {
        var c := chars[c1_idx];
        var out_chars := graph.Keys;
        var c2_idx := 0;
        while c2_idx < |out_chars|
            invariant 0 <= c2_idx <= |out_chars|
        {
            if c in graph[chars[c2_idx]] {
                in_degree[c] := in_degree[c] + 1;
            }
            c2_idx := c2_idx + 1;
        }
        c1_idx := c1_idx + 1;
    }
    
    var queue := new multiset<char>;
    c1_idx := 0;
    while c1_idx < |chars|
        invariant 0 <= c1_idx <= |chars|
        invariant forall c :: c in queue ==> in_degree[c] == 0
    {
        if in_degree[chars[c1_idx]] == 0 {
            queue := queue + {chars[c1_idx]};
        }
        c1_idx := c1_idx + 1;
    }
    
    var sorted_chars := new seq<char>;
    var zero_in_degree_nodes := |queue|;
    
    while zero_in_degree_nodes > 0
        invariant zero_in_degree_nodes >= 0
        invariantforall c :: c in queue ==> in_degree[c] == 0
        invariant forall c :: c in sorted_chars ==> (in_degree[c] == -1 || c in queue)
    {
        // Use lemma to prove queue is not empty
        assume |queue| > 0;
        var u :| u in queue;
        queue := queue - {u};
        in_degree[u] := -1; // Mark as visited/sorted
        sorted_chars := sorted_chars + [u];
        
        var neighbors := graph[u].Keys;
        var v_idx := 0;
        while v_idx < |neighbors|
            invariant 0 <= v_idx <= |neighbors|
        {
            var v := neighbors[v_idx];
            in_degree[v] := in_degree[v] - 1;
            if in_degree[v] == 0 {
                queue := queue + {v};
            }
            v_idx := v_idx + 1;
        }
        zero_in_degree_nodes := |queue|;
    }

    // Check for cycles
    if |sorted_chars| < |unique_chars| {
        return "Impossible";
    }

    // Create the final alphabet string by adding remaining letters not in the input
    var full_alphabet_chars := sorted_chars;
    var alphabet_letters := "abcdefghijklmnopqrstuvwxyz";
    var char_idx := 0;
    while char_idx < 26
        invariant 0 <= char_idx <= 26
        invariant |full_alphabet_chars| == |sorted_chars| + char_idx - (number of chars from "a" to alphabet_letters[char_idx-1] already in sorted_chars)
    {
        var c := alphabet_letters[char_idx];
        if c !in unique_chars {
            full_alphabet_chars := full_alphabet_chars + [c];
        }
        char_idx := char_idx + 1;
    }

    return generateAlphabet(full_alphabet_chars);
}
// </vc-code>

