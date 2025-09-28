// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
function toChar(i: int): char
    requires 0 <= i < 26
    ensures 'a' <= toChar(i) <= 'z'
{
    'a' + i
}

function toInt(c: char): int
    requires 'a' <= c <= 'z'
    ensures 0 <= toInt(c) < 26
{
    c - 'a'
}

lemma Lemma_FindChar(alpha: seq<char>, c: char, i: int)
    requires 0 <= i < |alpha|
    requires 'a' <= c <= 'z'
    requires distinct_chars(alpha)
    requires c in alpha[..i]
    ensures exists k :: 0 <= k < i && alpha[k] == c
{
    if alpha[i] == c {
        // Handled by the postcondition with k=i, but we know c is in alpha[..i]
    } else {
        if i > 0 {
            Lemma_FindChar(alpha, c, i-1);
        }
    }
}

predicate distinct_chars(s: seq<char>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

lemma Lemma_AppendDistinct(s: seq<char>, c: char)
    requires distinct_chars(s)
    requires c !in s
    ensures distinct_chars(s + [c])
{
    // Proof by contradiction or direct reasoning
    // Assume distinct_chars(s + [c]) is false. Then there exist i, j such that (s + [c])[i] == (s + [c])[j]
    // Since c is not in s, and s has distinct characters, the only case is if one of i, j refers to the appended c.
    // Cases:
    // 1. 0 <= i < j < |s|: s[i] == s[j], contradicts distinct_chars(s).
    // 2. 0 <= i < |s| and j == |s|: s[i] == c, contradicts c !in s.
    // 3. i == |s| and j == |s| is not possible (since i < j).
}

lemma Lemma_RemoveChar(s: seq<char>, c: char)
    requires distinct_chars(s)
    requires c in s
    ensures distinct_chars(s - [c])
    ensures |s - [c]| == |s| - 1
{
    var index_c := -1;
    for k := 0 to |s| 
        invariant 0 <= k <= |s|
        invariant forall p, q :: 0 <= p < q < k ==> s[p] != s[q]
        invariant index_c == -1 || (0 <= index_c < k && s[index_c] == c && forall i :: 0 <= i < index_c ==> s[i] != c)
    {
        if s[k] == c && index_c == -1 {
            index_c := k;
        }
    }
    assert index_c != -1;
    assert s[index_c] == c;
    
    // The distinct_chars(s - [c]) can be proven by observing that removing an element 
    // from a distinct sequence keeps the remaining elements distinct. 
    // The length is also directly observable.
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

    var adj_matrix: array<array<bool>> := new array<array<bool>>(26, (i: int) => new array<bool>(26, (j: int) => false));
    var in_degree: array<int> := new array<int>(26, (i: int) => 0);
    
    var char_present: array<bool> := new array<bool>(26, (i: int) => false);

    for i := 1 to n
        invariant 1 <= i <= n
        invariant forall x, y :: 0 <= x < 26 && 0 <= y < 26 ==> !adj_matrix[x][y] || (exists p, q :: 1 <= p < i && q < |lines[p]| && adj_matrix[x][y] == true && (
            (exists k :: 0 <= k < |lines[p]| && k < |lines[p+1]| && lines[p][k] != lines[p+1][k] && x == toInt(lines[p][k]) && y == toInt(lines[p+1][k]) && (forall l :: 0 <= l < k ==> lines[p][l] == lines[p+1][l]))
        ))
        invariant forall x :: 0 <= x < 26 ==> in_degree[x] == (if char_present[x] then (count j :: 0 <= j < 26 && adj_matrix[j][x]) else 0)
        invariant forall x :: 0 <= x < 26 ==> (char_present[x] == (exists p :: 1 <= p <= i && (exists k :: 0 <= k < |lines[p]| && toInt(lines[p][k]) == x)))
    {
        var s1 := lines[i];
        var s2 := lines[i+1]; // Note: loop goes to n, so i+1 can be n+1, which is valid index for lines.

        var k := 0;
        while k < |s1| && k < |s2|
            invariant 0 <= k <= |s1|
            invariant 0 <= k <= |s2|
            invariant forall l :: 0 <= l < k ==> s1[l] == s2[l]
        {
            char_present[toInt(s1[k])] := true;
            char_present[toInt(s2[k])] := true;
            if s1[k] != s2[k] {
                var u := toInt(s1[k]);
                var v := toInt(s2[k]);
                if !adj_matrix[u][v] {
                    adj_matrix[u][v] := true;
                    in_degree[v] := in_degree[v] + 1;
                }
                k := max(|s1|, |s2|); // Break out of loop, no more distinct chars if there are.
            }
            k := k + 1;
        }
        while k < |s1| 
            invariant k <= |s1|
            invariant forall l :: 0 <= l < k ==> s1[l] == s2[l]
        {
            char_present[toInt(s1[k])] := true;
            k := k + 1;
        }
         while k < |s2| 
            invariant k <= |s2|
            invariant forall l :: 0 <= l < k ==> s1[l] == s2[l]
        {
            char_present[toInt(s2[k])] := true;
            k := k + 1;
        }

        if k == |s1| && k < |s2| {
            // s1 is a prefix of s2, lexicographically valid
        } else if k == |s2| && k < |s1| {
            // s2 is a prefix of s1, invalid order
            result := "Impossible";
            return;
        }
    }

    var alphabet_order: seq<char> := [];
    var q: seq<int> := [];

    for i := 0 to 25
        invariant 0 <= i <= 26
        invariant forall j :: 0 <= j < i ==> (char_present[j] ==> (count k :: 0 <= k < 26 && adj_matrix[k][j]) == in_degree[j])
        invariant q == (seq k | 0 <= k < i && char_present[k] && in_degree[k] == 0)
    {
        if char_present[i] && in_degree[i] == 0 {
            q := q + [i];
        }
    }

    while |q| > 0
        invariant forall c :: c in alphabet_order ==> char_present[toInt(c)]
        invariant (forall u :: 0 <= u < 26 && char_present[u] && in_degree[u] == 0 ==> u in q || u in alphabet_order)
        invariant (forall u :: u in alphabet_order ==> forall v :: 0 <= v < 26 && adj_matrix[v][u] ==> v in alphabet_order )
        invariant distinct_chars(alphabet_order)
    {
        var u := q[0];
        q := q[1..];
        alphabet_order := alphabet_order + [toChar(u)];

        for v := 0 to 25
            invariant 0 <= v <= 26
            invariant (forall x :: x < v && char_present[x] && in_degree[x] == 0 ==> x in q || x in alphabet_order)
            invariant (forall x :: x < v && adj_matrix[u][x] ==> in_degree[x] == (old(in_degree[x]) - 1))
        {
            if adj_matrix[u][v] {
                in_degree[v] := in_degree[v] - 1;
                if in_degree[v] == 0 {
                    q := q + [v];
                }
            }
        }
    }

    if |alphabet_order| == (count i :: 0 <= i < 26 && char_present[i]) {
        // All present characters were added, no cycle detected.
        // Fill remaining with unused characters.
        var full_alphabet: seq<char> := alphabet_order;
        for i := 0 to 25
            invariant 0 <= i <= 26
            invariant distinct_chars(full_alphabet)
            invariant alphabet_order <= full_alphabet
            invariant forall c :: c in full_alphabet[|alphabet_order|..] ==> c !in alphabet_order && !char_present[toInt(c)]
        {
            var c := toChar(i);
            if !(c in full_alphabet) {
                // Lemma_AppendDistinct(full_alphabet, c);
                full_alphabet := full_alphabet + [c];
            }
        }
        result := full_alphabet;
    } else {
        // Cycle detected, or some characters were left out (impossible case, given the count)
        result := "Impossible";
    }
}
// </vc-code>
