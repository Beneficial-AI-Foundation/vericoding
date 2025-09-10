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
function getCharIndex(c: char, alphabet: string): int
  requires |alphabet| == 26
  requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
  requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
  requires 'a' <= c <= 'z'
  requires exists i :: 0 <= i < |alphabet| && alphabet[i] == c
  ensures 0 <= getCharIndex(c, alphabet) < |alphabet|
  ensures alphabet[getCharIndex(c, alphabet)] == c
{
  var i := 0;
  while i < |alphabet|
    invariant 0 <= i <= |alphabet|
    invariant forall k :: 0 <= k < i ==> alphabet[k] != c
  {
    if alphabet[i] == c then
      return i;
    i := i + 1;
  }
  assert false; // Should not reach here because c is guaranteed to be in alphabet
  return -1; // Dummy return
}

// Function to find the lexicographical difference between two strings s1 and s2
// Returns '1' if s1 < s2, '-1' if s1 > s2, '0' if s1 == s2
function compareStrings(s1: string, s2: string, alphabet: string): int
  requires |alphabet| == 26
  requires forall i :: 0 <= i < |alphabet| ==> 'a' <= alphabet[i] <= 'z'
  requires forall i, j :: 0 <= i < j < |alphabet| ==> alphabet[i] != alphabet[j]
  requires forall i :: 0 <= i < |s1| ==> 'a' <= s1[i] <= 'z'
  requires forall i :: 0 <= i < |s2| ==> 'a' <= s2[i] <= 'z'
  ensures (compareStrings(s1, s2, alphabet) == 1) == lexicographicallyLessOrEqual(s1, s2, alphabet) && s1 != s2
  ensures (compareStrings(s1, s2, alphabet) == -1) == (lexicographicallyLessOrEqual(s2, s1, alphabet) && s1 != s2)
  ensures (compareStrings(s1, s2, alphabet) == 0) == (s1 == s2)
{
  if s1 == s2 then
    0
  else if |s1| <= |s2| && s1 == s2[..|s1|] then
    1 // s1 is a prefix of s2
  else if |s2| < |s1| && s2 == s1[..|s2|] then
    -1 // s2 is a prefix of s1
  else
  {
    var i := 0;
    while i < |s1| && i < |s2| && s1[i] == s2[i]
      invariant 0 <= i <= |s1|
      invariant 0 <= i <= |s2|
      invariant forall k :: 0 <= k < i ==> s1[k] == s2[k]
    {
      i := i + 1;
    }
    if i < |s1| && i < |s2| then
      if alphabetOrder(s1[i], s2[i], alphabet) then 1 else -1
    else if i == |s1| && i < |s2| then
      1 // s1 is a prefix of s2
    else if i < |s1| && i == |s2| then
      -1 // s2 is a prefix of s1
    else
      0 // Should not happen, implies s1 == s2 already handled
  }
}

// Helper to check if a permutation is valid given the constraints
predicate isValidPermutation(permutation: string, constraints: set<(char, char)>)
  requires |permutation| == 26
  requires forall i :: 0 <= i < |permutation| ==> 'a' <= permutation[i] <= 'z'
  requires forall i, j :: 0 <= i < j < |permutation| ==> permutation[i] != permutation[j]
{
  forall c1, c2 :: (c1, c2) in constraints ==> alphabetOrder(c1, c2, permutation)
}

predicate isPermutationOfAlphabet(s: string)
  requires |s| == 26
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  var counts := map<char, int>();
  var c := 'a';
  while c <= 'z'
    invariant forall k :: 'a' <= k < c ==> counts[k] == 0
    invariant c <= '{' // 'z' + 1
  {
    counts := counts[c := 0];
    c := c + 1;
  }

  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> counts[s[k]] == 1
    invariant (forall k :: 'a' <= k <= 'z' ==> (counts.Contains(k) && counts[k] == (if exists j :: 0 <= j < i && s[j] == k then 1 else 0)))
  {
    if counts.Contains(s[i]) then
      counts := counts[s[i] := counts[s[i]] + 1];
    else
      counts := counts[s[i] := 1];
    i := i + 1;
  }

  (forall k :: 'a' <= k <= 'z' ==> counts.Contains(k) && counts[k] == 1)
}

// Topological sort helper method
method TopoSort(adj: map<char, set<char>>) returns (result: string)
  requires forall c1 :: adj.Contains(c1) ==> forall c2 :: c2 in adj[c1] ==> adj.Contains(c2)
  requires forall c :: 'a' <= c <= 'z' ==> adj.Contains(c)
  requires forall c :: 'a' <= c <= 'z' ==> adj[c] <= {'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'}
  requires forall src, dest :: (src, dest) in GetEdges(adj) ==> !IsPath(adj, dest, src) // No cycles
  ensures result == "Impossible" || (|result| == 26 && isPermutationOfAlphabet(result))
  ensures result == "Impossible" || (forall c1, c2 :: c2 in adj[c1] ==> alphabetOrder(c1, c2, result))
{
  var inDegree := map<char, int>();
  var q := new queue<char>();
  var orderedChars := new char[26];
  var k := 0; // index for orderedChars array

  var ch := 'a';
  while ch <= 'z'
    invariant 'a' <= ch <= 'z' + 1
    invariant forall c' :: 'a' <= c' < ch ==> inDegree.Contains(c')
    invariant forall c1,c2 :: 'a' <= c1 <= 'z' && 'a' <= c2 <= 'z' && c2 in adj[c1] ==> inDegree.Contains(c1) && inDegree.Contains(c2)
  {
    inDegree := inDegree[ch := 0];
    ch := ch + 1;
  }
 
  ch := 'a';
  while ch <= 'z'
    invariant 'a' <= ch <= 'z' + 1
    invariant forall c_key, c_val :: 'a' <= c_key < ch && c_val in adj[c_key] ==> inDegree.Contains(c_val) && inDegree[c_val] >= 0
    invariant forall c_key :: 'a' <= c_key < ch ==> inDegree.Contains(c_key)
  {
    var dests := adj[ch];
    for c_prime in dests {
      inDegree := inDegree[c_prime := inDegree[c_prime] + 1];
    }
    ch := ch + 1;
  }

  ch := 'a';
  while ch <= 'z'
    invariant 'a' <= ch <= 'z' + 1
    invariant forall c_key :: 'a' <= c_key < ch ==> inDegree.Contains(c_key)
    invariant forall c_key :: 'a' <= c_key < ch ==> inDegree[c_key] >= 0
    invariant forall c_inQ :: c_inQ in q.seq ==> inDegree[c_inQ] == 0
  {
    if inDegree[ch] == 0 {
      q.enqueue(ch);
    }
    ch := ch + 1;
  }

  while !q.IsEmpty()
    invariant k <= 26
    invariant forall i :: 0 <= i < k ==> inDegree[orderedChars[i]] == -1 //标记为已处理
    invariant forall c :: 'a' <= c <= 'z' ==> inDegree.Contains(c)
    invariant forall c' :: c' in q.seq ==> inDegree[c'] == 0
    invariant forall c1, c2 :: 'a' <= c1 <= 'z' && 'a' <= c2 <= 'z' && c2 in adj[c1] && inDegree[c1] == -1 && inDegree[c2] != -1 ==> (inDegree[c2] >= 0)
    invariant forall c :: ('a' <= c <= 'z' && inDegree[c] >= 0) ==> ! (exists i :: 0 <= i < k && orderedChars[i] == c)
  {
    var u := q.dequeue();
    orderedChars[k] := u;
    k := k + 1;
    inDegree := inDegree[u := -1]; // Mark as processed

    for v in adj[u] {
      if inDegree[v] != -1 { // Only update if not yet processed
        inDegree := inDegree[v := inDegree[v] - 1];
        if inDegree[v] == 0 {
          q.enqueue(v);
        }
      }
    }
  }

  if k == 26 then
    result := new string(orderedChars);
  else
    result := "Impossible";
}

// BFS to check for cycles
function IsPath(adj: map<char, set<char>>, startNode: char, endNode: char): bool
  reads adj
  requires forall c :: 'a' <= c <= 'z' ==> adj.Contains(c)
  requires forall c1 :: adj.Contains(c1) ==> forall c2 :: c2 in adj[c1] ==> adj.Contains(c2)
{
  var visited := set<char>();
  var q := new queue<char>();
  q.enqueue(startNode);
  visited := visited + {startNode};

  while !q.IsEmpty()
    invariant forall c :: c in q.seq ==> c in visited
    invariant forall c :: c in visited && !(c in q.seq) ==> (old(q.seq) == ([c] + q.seq) ==> c is processed)
  {
    var u := q.dequeue();
    if u == endNode then
      return true;

    for v in adj[u] {
      if !(v in visited) {
        visited := visited + {v};
        q.enqueue(v);
      }
    }
  }
  return false;
}

function GetEdges(adj: map<char, set<char>>): set<(char, char)>
  reads adj
  requires forall c :: 'a' <= c <= 'z' ==> adj.Contains(c)
  ensures forall c1, c2 :: (c1, c2) in GetEdges(adj) <==> c2 in adj[c1]
{
  var edges := set<(char, char)>();
  var ch := 'a';
  while ch <= 'z'
    invariant 'a' <= ch <= 'z' + 1
    invariant forall c1 :: 'a' <= c1 < ch ==> (forall c2 :: (c1, c2) in edges <==> c2 in adj[c1])
  {
    for dest in adj[ch] {
      edges := edges + {(ch, dest)};
    }
    ch := ch + 1;
  }
  return edges;
}

// Queue for BFS/Topological Sort
class queue<T> {
  var elements: seq<T>;

  constructor()
    ensures elements == []
  {
    elements := [];
  }

  method Enqueue(value: T)
    ensures elements == old(elements) + [value]
  {
    elements := elements + [value];
  }

  method Dequeue() returns (value: T)
    requires |elements| > 0
    ensures value == old(elements[0])
    ensures elements == old(elements)[1..]
  {
    value := elements[0];
    elements := elements[1..];
  }

  function IsEmpty(): bool
    ensures IsEmpty() == (|elements| == 0)
  {
    return |elements| == 0;
  }

  function size(): nat
    ensures size() == |elements|
  {
    return |elements|;
  }

  function seq(): seq<T>
  {
    return elements;
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
    var inputLines := parseInput(stdin_input);
    var n := parseInt(inputLines[0]);

    var words := new string[n];
    for i := 0 to n - 1 {
        words[i] := inputLines[i + 1];
    }

    var adj := map<char, set<char>>();
    var ch := 'a';
    while ch <= 'z'
        invariant 'a' <= ch <= 'z' + 1
        invariant forall c' :: 'a' <= c' < ch ==> adj.Contains(c') && adj[c'] == set{}
    {
        adj := adj[ch := set()];
        ch := ch + 1;
    }

    for i := 0 to n - 2
        invariant 0 <= i <= n - 1
        invariant forall c1, c2 :: ('a' <= c1 <= 'z' && 'a' <= c2 <= 'z' && c2 in adj[c1]) ==>
            (exists a, b :: 0 <= a <= i && 0 <= b < |words[a]| && b < |words[a+1]| && words[a][b] == c1 && words[a+1][b] == c2 && (forall k :: 0 <= k < b ==> words[a][k] == words[a+1][k]))
    {
        var s1 := words[i];
        var s2 := words[i+1];
        var minLen := |s1|;
        if |s2| < minLen then
            minLen := |s2];

        var diffFound := false;
        var j := 0;
        while j < minLen
            invariant 0 <= j <= minLen
            invariant !diffFound ==> forall k :: 0 <= k < j ==> s1[k] == s2[k]
        {
            if s1[j] != s2[j] then
                if IsPath(adj, s2[j], s1[j]) then // Check for cycle
                    return "Impossible";
                adj := adj[s1[j]] := adj[s1[j]] + {s2[j]};
                diffFound := true;
                break;
            j := j + 1;
        }
        if !diffFound && |s1| > |s2| then // s2 is a prefix of s1, but s1 != s2
            return "Impossible";
    }

    result := TopoSort(adj);
}
// </vc-code>

