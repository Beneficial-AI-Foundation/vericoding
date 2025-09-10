predicate ValidInput(input: string)
{
    var lines := Split(input, '\n');
    |lines| >= 1 && 
    (var firstLine := Split(lines[0], ' ');
     |firstLine| == 2 &&
     StringToInt(firstLine[0]) > 0 && StringToInt(firstLine[1]) > 0 &&
     (var n := StringToInt(firstLine[0]);
      var m := StringToInt(firstLine[1]);
      n >= 3 && m >= 3 && |lines| >= n + 1 &&
      (forall i :: 1 <= i <= n ==> i < |lines| && |lines[i]| >= m) &&
      (forall i :: 1 <= i <= n ==> forall j :: 0 <= j < m ==> lines[i][j] in {'*', '.'})))
}

ghost predicate ExistsValidStarDecomposition(input: string)
requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var firstLine := Split(lines[0], ' ');
    var n := StringToInt(firstLine[0]);
    var m := StringToInt(firstLine[1]);

    exists k: int, stars: seq<(int, int, int)> :: 
        0 <= k <= n * m && |stars| == k &&
        (forall s :: s in stars ==> 
            1 <= s.0 <= n && 1 <= s.1 <= m && 1 <= s.2 <= min(n, m)) &&
        ValidStarDecomposition(input, stars)
}

predicate ValidStarDecomposition(input: string, stars: seq<(int, int, int)>)
requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var firstLine := Split(lines[0], ' ');
    var n := StringToInt(firstLine[0]);
    var m := StringToInt(firstLine[1]);
    // Each star is valid and within bounds
    (forall s :: s in stars ==> 
        s.0 >= 1 && s.0 <= n && s.1 >= 1 && s.1 <= m && s.2 > 0 &&
        ValidStar(n, m, s.0, s.1, s.2)) &&
    // The stars exactly cover all '*' positions
    (forall i, j :: 1 <= i <= n && 1 <= j <= m ==>
        (lines[i][j-1] == '*' <==> CoveredByStars(stars, i, j)) &&
        (lines[i][j-1] == '.' <==> !CoveredByStars(stars, i, j)))
}

predicate ValidStar(n: int, m: int, x: int, y: int, s: int)
{
    x >= 1 && x <= n && y >= 1 && y <= m && s > 0 &&
    x - s >= 1 && x + s <= n && y - s >= 1 && y + s <= m
}

predicate CoveredByStars(stars: seq<(int, int, int)>, i: int, j: int)
{
    exists s :: s in stars && CoveredByStar(s.0, s.1, s.2, i, j)
}

predicate CoveredByStar(x: int, y: int, size: int, i: int, j: int)
{
    (i == x && j == y) || // center
    (i == x && 1 <= AbsInt(j - y) <= size) || // horizontal ray
    (j == y && 1 <= AbsInt(i - x) <= size)    // vertical ray
}

predicate StartsWithIntAndValidFormat(s: string, k: int)
{
    |s| > 0 && 
    |IntToString(k)| <= |s| && 
    s[..|IntToString(k)|] == IntToString(k)
}

function FormatStarOutput(k: int, stars: seq<(int, int, int)>): string
requires k >= 0 && |stars| == k
{
    var result := IntToString(k) + "\n";
    var idx := 0;
    FormatStarOutputHelper(result, stars, idx)
}

function FormatStarOutputHelper(result: string, stars: seq<(int, int, int)>, idx: int): string
requires 0 <= idx <= |stars|
decreases |stars| - idx
{
    if idx >= |stars| then result
    else 
        var newResult := result + IntToString(stars[idx].0) + " " + IntToString(stars[idx].1) + " " + IntToString(stars[idx].2) + "\n";
        FormatStarOutputHelper(newResult, stars, idx + 1)
}

// <vc-helpers>
function Split(s: string, sep: char): seq<string>
{
  if |s| == 0 then []
  else if s[0] == sep then [""] + Split(s[1..], sep)
  else
    var rest := Split(s[1..], sep);
    [s[0] + (if |rest| > 0 then rest[0] else "")] + (if |rest| > 0 then rest[1..] else [])
}

function StringToInt(s: string): int
{
  if |s| == 0 then -1
  else if s[0] == '-' then -StringToInt(s[1..])
  else var n := 0;
       var i := 0;
       while i < |s| && '0' <= s[i] <= '9'
         invariant 0 <= i <= |s|
         invariant n >= 0
       {
         n := n * 10 + (s[i] as int - '0' as int);
         i := i + 1;
       }
       if i == 0 then -1 else n
}

function IntToString(x: int): string
{
  if x < 0 then "-" + IntToString(-x)
  else if x == 0 then "0"
  else if x < 10 then [('0' as int + x) as char]
  else IntToString(x / 10) + [('0' as int + (x % 10)) as char]
}

function AbsInt(x: int): int
{
  if x < 0 then -x else x
}

function min(a: int, b: int): int
{
  if a <= b then a else b
}

lemma {:vcs_split_on_every_assert} SplitLemma(s: string, sep: char)
ensures |Split(s, sep)| >= 1
ensures forall i :: 0 <= i < |Split(s, sep)| ==> |Split(s, sep)[i]| >= 0
{
}

lemma {:vcs_split_on_every_assert} StringToIntLemma(s: string)
ensures StringToInt(s) >= 0 || StringToInt(s) == -1
{
}

lemma {:vcs_split_on_every_assert} AbsIntLemma(x: int)
ensures AbsInt(x) >= 0
{
}

lemma {:vcs_split_on_every_assert} IntToStringLemma(x: int)
ensures |IntToString(x)| >= 1
{
}

lemma {:vcs_split_on_every_assert} ValidStarCoverageLemma(n: int, m: int, x: int, y: int, s: int, i: int, j: int)
requires ValidStar(n, m, x, y, s)
requires CoveredByStar(x, y, s, i, j)
ensures 1 <= i <= n && 1 <= j <= m
{
}

lemma {:vcs_split_on_every_assert} StarDecompositionCoverageLemma(input: string, stars: seq<(int, int, int)>)
requires ValidInput(input)
requires ValidStarDecomposition(input, stars)
ensures var lines := Split(input, '\n');
        var firstLine := Split(lines[0], ' ');
        var n := StringToInt(firstLine[0]);
        var m := StringToInt(firstLine[1]);
        forall i, j :: 1 <= i <= n && 1 <= j <= m ==> 
            (lines[i][j-1] == '*' <==> CoveredByStars(stars, i, j)) &&
            (lines[i][j-1] == '.' <==> !CoveredByStars(stars, i, j))
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires |input| > 0
ensures ValidInput(input) ==> 
    (result == "-1\n" <==> !ExistsValidStarDecomposition(input))
ensures ValidInput(input) && result != "-1\n" ==>
    (exists k: int, stars: seq<(int, int, int)> ::
        k >= 0 && |stars| == k &&
        ValidStarDecomposition(input, stars) &&
        result == FormatStarOutput(k, stars))
ensures ValidInput(input) ==> result != ""
ensures !ValidInput(input) ==> result == "-1\n"
ensures result == "-1\n" || (exists k: int :: k >= 0 && StartsWithIntAndValidFormat(result, k))
ensures result == "" || result[|result|-1..] == "\n"
// </vc-spec>
// <vc-code>
{
    if !ValidInput(input) {
        result := "-1\n";
        return;
    }
    
    var lines := Split(input, '\n');
    var firstLine := Split(lines[0], ' ');
    var n := StringToInt(firstLine[0]);
    var m := StringToInt(firstLine[1]);
    
    var grid := lines[1..n+1];
    var stars: seq<(int, int, int)> := [];
    var k := 0;
    
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant |stars| == k
        invariant forall s :: s in stars ==> ValidStar(n, m, s.0, s.1, s.2)
    {
        var j := 1;
        while j <= m
            invariant 1 <= j <= m+1
            invariant |stars| == k
            invariant forall s :: s in stars ==> ValidStar(n, m, s.0, s.1, s.2)
        {
            if grid[i-1][0] == '*' {
                var maxSize := min(min(i-1, n-i), min(j-1, m-j));
                var found := false;
                var size := 1;
                
                while size <= maxSize && !found
                    invariant 1 <= size <= maxSize+1
                    invariant |stars| == k
                {
                    if ValidStar(n, m, i, j, size) &&
                       grid[i-1][0] == '*' &&
                       grid[i-size-1][0] == '*' &&
                       grid[i+size-1][0] == '*' &&
                       grid[i-1][size-1] == '*' &&
                       grid[i-1][size+1] == '*'
                    {
                        stars := stars + [(i, j, size)];
                        k := k + 1;
                        found := true;
                    }
                    size := size + 1;
                }
                
                if !found {
                    result := "-1\n";
                    return;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    if ValidStarDecomposition(input, stars) {
        result := FormatStarOutput(k, stars);
    } else {
        result := "-1\n";
    }
}
// </vc-code>

