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
// No additional helpers needed for this implementation
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
  assert |lines| == n + 1;
  assert n >= 1;
  var stringList := lines[1..];
  assert |stringList| == n;
  var letters: seq<char> := ['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z'];
  var graph: map<char, set<char>> := map[];
  var indegree: map<char, int> := map[];
  for i := 0 <= i < 26 {
    var c := letters[i];
    graph := graph[c := {}];
    indegree := indegree[c := 0];
  }
  var impossible := false;
  for i := 0 <= i < n - 1 {
    var s1 := stringList[i];
    var s2 := stringList[i + 1];
    var len := min(|s1|, |s2|);
    var k := 0;
    while k < len && s1[k] == s2[k] {
      k := k + 1;
    }
    if k == len {
      if |s1| > |s2| {
        impossible := true;
      }
    } else {
      var c1 := s1[k];
      var c2 := s2[k];
      if c1 !in graph {
        graph := graph[c1 := {}];
        indegree := indegree[c1 := 0];
      }
      if c2 !in graph {
        graph := graph[c2 := {}];
        indegree := indegree[c2 := 0];
      }
      graph := graph[c1 := graph[c1] + {c2}];
      indegree := indegree[c2 := (if c2 in indegree then indegree[c2] else 0) + 1];
    }
  }
  if impossible {
    result := "Impossible";
    return;
  }
  var queue: seq<char> := [];
  for c in letters {
    if indegree[c] == 0 {
      queue := queue + [c];
    }
  }
  var resultSeq: seq<char> := [];
  var processed: set<char> := {};
  while |queue| > 0 {
    var c := queue[0];
    queue := queue[1..];
    processed := processed + {c};
    resultSeq := resultSeq + [c];
    for next in graph[c] {
      indegree := indegree[next := indegree[next] - 1];
      if indegree[next] == 0 && next !in processed {
        queue := queue + [next];
      }
    }
  }
  if |resultSeq| < 26 {
    result := "Impossible";
  } else {
    var alphabet: seq<char> := resultSeq;
    var res := "";
    for c in alphabet {
      res := res + [c];
    }
    result := res;
  }
}
// </vc-code>

