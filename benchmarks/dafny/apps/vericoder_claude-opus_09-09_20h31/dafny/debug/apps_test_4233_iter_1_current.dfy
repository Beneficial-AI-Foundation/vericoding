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
function Split(s: string, delimiter: char): seq<string>

function StringToInt(s: string): int

function IntToString(n: int): string

function AbsInt(x: int): int
{
    if x < 0 then -x else x
}

function min(a: int, b: int): int
{
    if a < b then a else b
}

predicate IsStarAt(lines: seq<string>, n: int, m: int, x: int, y: int, s: int)
requires |lines| > n && n >= 1 && m >= 1
requires 1 <= x <= n && 1 <= y <= m
requires forall i :: 1 <= i <= n ==> |lines[i]| >= m
{
    s > 0 && ValidStar(n, m, x, y, s) &&
    // Center must be '*'
    lines[x][y-1] == '*' &&
    // Check all rays are '*'
    (forall d :: 1 <= d <= s ==> 
        lines[x][y-1+d] == '*' && lines[x][y-1-d] == '*' &&
        lines[x+d][y-1] == '*' && lines[x-d][y-1] == '*')
}

function MaxStarSize(lines: seq<string>, n: int, m: int, x: int, y: int): int
requires |lines| > n && n >= 1 && m >= 1
requires 1 <= x <= n && 1 <= y <= m
requires forall i :: 1 <= i <= n ==> |lines[i]| >= m
{
    var maxPossible := min(min(x-1, n-x), min(y-1, m-y));
    MaxStarSizeHelper(lines, n, m, x, y, maxPossible)
}

function MaxStarSizeHelper(lines: seq<string>, n: int, m: int, x: int, y: int, s: int): int
requires |lines| > n && n >= 1 && m >= 1
requires 1 <= x <= n && 1 <= y <= m
requires forall i :: 1 <= i <= n ==> |lines[i]| >= m
requires s >= 0
decreases s
{
    if s == 0 then 0
    else if IsStarAt(lines, n, m, x, y, s) then s
    else MaxStarSizeHelper(lines, n, m, x, y, s-1)
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
        return "-1\n";
    }
    
    var lines := Split(input, '\n');
    var firstLine := Split(lines[0], ' ');
    var n := StringToInt(firstLine[0]);
    var m := StringToInt(firstLine[1]);
    
    // Create a grid to track which cells are covered
    var covered := new bool[n+1, m+1];
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant forall x, y :: 1 <= x < i && 1 <= y <= m ==> covered[x,y] == false
    {
        var j := 1;
        while j <= m
            invariant 1 <= j <= m+1
            invariant forall x, y :: 1 <= x < i && 1 <= y <= m ==> covered[x,y] == false
            invariant forall y :: 1 <= y < j ==> covered[i,y] == false
        {
            covered[i,j] := false;
            j := j + 1;
        }
        i := i + 1;
    }
    
    var stars: seq<(int, int, int)> := [];
    
    // Try to find stars greedily, prioritizing larger stars
    i := 1;
    while i <= n
        invariant 1 <= i <= n+1
    {
        var j := 1;
        while j <= m
            invariant 1 <= j <= m+1
        {
            if lines[i][j-1] == '*' && !covered[i,j] {
                // Find the maximum star size centered at (i,j)
                var maxSize := MaxStarSize(lines, n, m, i, j);
                if maxSize > 0 {
                    // Add this star
                    stars := stars + [(i, j, maxSize)];
                    
                    // Mark all cells covered by this star
                    covered[i,j] := true;
                    var d := 1;
                    while d <= maxSize
                        invariant 1 <= d <= maxSize + 1
                    {
                        if i+d <= n { covered[i+d,j] := true; }
                        if i-d >= 1 { covered[i-d,j] := true; }
                        if j+d <= m { covered[i,j+d] := true; }
                        if j-d >= 1 { covered[i,j-d] := true; }
                        d := d + 1;
                    }
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Check if all '*' cells are covered
    var allCovered := true;
    i := 1;
    while i <= n && allCovered
        invariant 1 <= i <= n+1
    {
        var j := 1;
        while j <= m && allCovered
            invariant 1 <= j <= m+1
        {
            if lines[i][j-1] == '*' && !covered[i,j] {
                allCovered := false;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    if !allCovered {
        return "-1\n";
    }
    
    // Check that no '.' cells are covered
    var noDotsCovered := true;
    i := 1;
    while i <= n && noDotsCovered
        invariant 1 <= i <= n+1
    {
        var j := 1;
        while j <= m && noDotsCovered
            invariant 1 <= j <= m+1
        {
            if lines[i][j-1] == '.' && covered[i,j] {
                noDotsCovered := false;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    if !noDotsCovered {
        return "-1\n";
    }
    
    return FormatStarOutput(|stars|, stars);
}
// </vc-code>

