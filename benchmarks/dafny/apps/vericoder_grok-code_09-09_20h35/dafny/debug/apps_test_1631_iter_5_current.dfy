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
  var n : int := parseInt(lines[0]);
  var used: set<char> := {};
  for i := 1 to n {
    var s := lines[i];
    for j := 0 to |s|-1 {
      used := used + {s[j]};
    }
  }
  var constraints: set<(char, char)> := {};
  for i := 1 to n-1 {
    var s1 := lines[i];
    var s2 := lines[i+1];
    var k := 0;
    while k < |s1| && k < |s2| {
      if s1[k] != s2[k] {
        constraints := constraints + {(s1[k], s2[k])};
        break;
      }
      k := k + 1;
    }
  }
  var indegree: map<char, int> := map[];
  for c in used {
    indegree := indegree[c := 0];
  }
  for p in constraints {
    indegree := indegree[p.1 := indegree[p.1] + 1];
  }
  var graph: map<char, set<char>> := map[];
  for p in constraints {
    graph := graph[p.0 := if p.0 in graph then graph[p.0] + {p.1} else {p.1}];
  }
  var queue: seq<char> := [];
  for c in used {
    if indegree[c] == 0 {
      queue := queue + [c];
    }
  }
  var topOrder: seq<char> := [];
  while |queue| > 0 {
    var cur := queue[0];
    queue := queue[1..];
    topOrder := topOrder + [cur];
    for neighbor in graph[cur] {
      indegree := indegree[neighbor := indegree[neighbor] - 1];
      if indegree[neighbor] == 0 {
        queue := queue + [neighbor];
      }
    }
  }
  if |topOrder| < |used| {
    result := "Impossible";
  } else {
    var remaining: seq<char> := [];
    for i := 0 to 25 {
      var c := ('a' as char) + i;
      if !(c in used) {
        remaining := remaining + [c];
      }
    }
    result := topOrder + remaining;
  }
}
// </vc-code>

