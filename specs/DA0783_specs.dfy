// <vc-preamble>
predicate wellFormedInput(input: string)
{
    |input| > 0 && 
    (exists lines :: lines == splitLines(input) && |lines| > 0)
}

predicate isNumericString(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function parseInput(input: string): (int, int, int, int, int, int, seq<(int, int, int)>, seq<(int, int)>, seq<(int, int)>)
  requires wellFormedInput(input)
  ensures var (n, m, s, b, k, h, spaceships, bases, edges) := parseInput(input);
          1 <= n <= 100 && 0 <= m <= 10000 && 1 <= s <= 1000 && 1 <= b <= 1000 &&
          0 <= k <= 1000000000 && 0 <= h <= 1000000000 &&
          |spaceships| == s && |bases| == b && |edges| == m
{
    (1, 0, 1, 1, 0, 0, [(1, 0, 0)], [(1, 0)], [])
}

function computeFloydWarshall(n: int, edges: seq<(int, int)>): seq<seq<int>>
  requires n >= 1
  ensures |computeFloydWarshall(n, edges)| == n
  ensures forall i :: 0 <= i < n ==> |computeFloydWarshall(n, edges)[i]| == n
  ensures forall i :: 0 <= i < n ==> computeFloydWarshall(n, edges)[i][i] == 0
  ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> computeFloydWarshall(n, edges)[i][j] >= 0
{
    seq(n, i => seq(n, j => if i == j then 0 else 1000000))
}

function computeMaxBipartiteMatching(spaceships: seq<(int, int, int)>, bases: seq<(int, int)>, 
                                    shortestPaths: seq<seq<int>>): int
  requires |shortestPaths| > 0 ==> (forall i :: 0 <= i < |shortestPaths| ==> |shortestPaths[i]| == |shortestPaths|)
  ensures computeMaxBipartiteMatching(spaceships, bases, shortestPaths) >= 0
  ensures computeMaxBipartiteMatching(spaceships, bases, shortestPaths) <= min(|spaceships|, |bases|)
  ensures forall i :: 0 <= i < |spaceships| ==> 
    var (x, a, f) := spaceships[i];
    (forall j :: 0 <= j < |bases| ==> 
      var (y, d) := bases[j];
      (x >= 1 && y >= 1 && |shortestPaths| > 0 && x-1 < |shortestPaths| && y-1 < |shortestPaths[0]| && 
       a >= d && shortestPaths[x-1][y-1] <= f)) 
    ==> computeMaxBipartiteMatching(spaceships, bases, shortestPaths) <= |bases|
{
    0
}

function min(a: int, b: int): int
  ensures min(a, b) <= a && min(a, b) <= b
  ensures min(a, b) == a || min(a, b) == b
{
    if a <= b then a else b
}
// </vc-preamble>

// <vc-helpers>
function splitLines(input: string): seq<string>
{
    [input]
}

function stringToInt(s: string): int
  requires isNumericString(s)
  ensures stringToInt(s) >= 0
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else stringToInt(s[..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function intToString(n: int): string
  requires n >= 0
  ensures isNumericString(intToString(n))
  ensures stringToInt(intToString(n)) == n
{
    if n == 0 then "0" else intToStringHelper(n)
}

function intToStringHelper(n: int): string
  requires n > 0
  ensures isNumericString(intToStringHelper(n))
  ensures stringToInt(intToStringHelper(n)) == n
  decreases n
{
    if n < 10 then 
        [('0' as int + n) as char]
    else
        intToStringHelper(n / 10) + [('0' as int + (n % 10)) as char]
}

function max(a: int, b: int): int
  ensures max(a, b) >= a && max(a, b) >= b
  ensures max(a, b) == a || max(a, b) == b
{
    if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires wellFormedInput(stdin_input)
  requires var parsed := parseInput(stdin_input);
           var (n, m, s, b, k, h, spaceships, bases, edges) := parsed;
           1 <= n <= 100 && 0 <= m <= 10000 && 1 <= s <= 1000 && 1 <= b <= 1000 &&
           0 <= k <= 1000000000 && 0 <= h <= 1000000000
  requires var parsed := parseInput(stdin_input);
           var (n, m, s, b, k, h, spaceships, bases, edges) := parsed;
           |spaceships| == s && |bases| == b && |edges| == m
  requires var parsed := parseInput(stdin_input);
           var (n, m, s, b, k, h, spaceships, bases, edges) := parsed;
           forall i :: 0 <= i < |spaceships| ==> 
             var (x, a, f) := spaceships[i];
             1 <= x <= n && 0 <= a <= 1000000000 && 0 <= f <= 1000000000
  requires var parsed := parseInput(stdin_input);
           var (n, m, s, b, k, h, spaceships, bases, edges) := parsed;
           forall i :: 0 <= i < |bases| ==> 
             var (x, d) := bases[i];
             1 <= x <= n && 0 <= d <= 1000000000
  requires var parsed := parseInput(stdin_input);
           var (n, m, s, b, k, h, spaceships, bases, edges) := parsed;
           forall i :: 0 <= i < |edges| ==> 
             var (u, v) := edges[i];
             1 <= u <= n && 1 <= v <= n
  ensures |result| > 0
  ensures isNumericString(result)
  ensures var parsed := parseInput(stdin_input);
          var (n, m, s, b, k, h, spaceships, bases, edges) := parsed;
          var numResult := stringToInt(result);
          numResult >= 0
  ensures var parsed := parseInput(stdin_input);
          var (n, m, s, b, k, h, spaceships, bases, edges) := parsed;
          var numResult := stringToInt(result);
          numResult <= h * s
  ensures var parsed := parseInput(stdin_input);
          var (n, m, s, b, k, h, spaceships, bases, edges) := parsed;
          var shortestPaths := computeFloydWarshall(n, edges);
          var maxMatching := computeMaxBipartiteMatching(spaceships, bases, shortestPaths);
          var numResult := stringToInt(result);
          numResult == min(maxMatching * k, h * s)
  ensures var parsed := parseInput(stdin_input);
          var (n, m, s, b, k, h, spaceships, bases, edges) := parsed;
          var shortestPaths := computeFloydWarshall(n, edges);
          var maxMatching := computeMaxBipartiteMatching(spaceships, bases, shortestPaths);
          var numResult := stringToInt(result);
          maxMatching * k <= h * s ==> numResult == maxMatching * k
  ensures var parsed := parseInput(stdin_input);
          var (n, m, s, b, k, h, spaceships, bases, edges) := parsed;
          var shortestPaths := computeFloydWarshall(n, edges);
          var maxMatching := computeMaxBipartiteMatching(spaceships, bases, shortestPaths);
          var numResult := stringToInt(result);
          maxMatching * k > h * s ==> numResult == h * s
// </vc-spec>
// <vc-code>
{
    var parsed := parseInput(stdin_input);
    var (n, m, s, b, k, h, spaceships, bases, edges) := parsed;

    var shortestPaths := computeFloydWarshall(n, edges);
    var maxMatching := computeMaxBipartiteMatching(spaceships, bases, shortestPaths);

    var attackCost := maxMatching * k;
    var dummyCost := h * s;
    var minCost := min(attackCost, dummyCost);

    result := intToString(minCost);
}
// </vc-code>
