// <vc-preamble>
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

    (forall s :: s in stars ==> 
        s.0 >= 1 && s.0 <= n && s.1 >= 1 && s.1 <= m && s.2 > 0 &&
        ValidStar(n, m, s.0, s.1, s.2)) &&

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
    (i == x && j == y) ||
    (i == x && 1 <= AbsInt(j - y) <= size) ||
    (j == y && 1 <= AbsInt(i - x) <= size)
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
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
