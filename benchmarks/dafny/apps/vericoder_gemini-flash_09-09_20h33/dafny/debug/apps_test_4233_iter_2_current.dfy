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
function AbsInt(x: int): int
{
    if x < 0 then -x else x
}

function min(a: int, b: int): int
{
    if a < b then a else b
}

function StringToInt(s: string): int
reads s
requires forall c :: c in s ==> '0' <= c <= '9'
requires |s| > 0
ensures StringToInt(s) >= 0
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res == (if i == 0 then 0 else StringToInt(s[..i]))
    {
        res := res * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    res
}

function IntToString(n: int): string
reads n
requires n >= 0
ensures forall c :: c in IntToString(n) ==> '0' <= c <= '9'
ensures (n == 0) ==> (IntToString(n) == "0")
ensures (n > 0) ==> (|IntToString(n)| > 0)
{
    if n == 0 then "0"
    else
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant s == IntReverseString(n, temp, s)
        {
            s := (temp % 10 as char) + s;
            temp := temp / 10;
        }
        s
}
function IntReverseString(n: int, temp: int, s: string): string
reads n, temp, s
requires n >= 0 && temp >= 0
{
    if temp == n then ""
    else if temp == 0 then s
    else IntReverseString(n, temp/10, ((temp % 10 as char) + s))
}

function Split(s: string, delimiter: char): seq<string>
reads s
{
    var result: seq<string> := [];
    var currentWord := "";
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i && s[j] != delimiter ==> s[j] in currentWord || (exists k :: 0 <= k < |result| && s[j] in result[k])
        invariant forall j :: 0 <= j < |result| ==> delimiter !in result[j]
    {
        if i < |s| && s[i] != delimiter {
            currentWord := currentWord + s[i];
        } else {
            result := result + [currentWord];
            currentWord := "";
        }
    }
    result
}

predicate IsValidGridChar(c: char) {
    c == '*' || c == '.'
}

lemma CharToBool(c: char): bool
ensures (c == '*') == true
ensures (c == '.') == false
{
    c == '*'
}

// Helper to check if a specific cell (r, c) contains a star centered at (sr, sc) with size ss
function StarCovers(sr: int, sc: int, ss: int, r: int, c: int): bool
{
    (r == sr && c == sc) || // Center
    (r == sr && AbsInt(c - sc) <= ss) || // Horizontal arm
    (c == sc && AbsInt(r - sr) <= ss)    // Vertical arm
}

// Function to find the maximum possible size of a star centered at (r, c)
function MaxStarSize(grid: seq<seq<char>>, n: int, m: int, r: int, c: int): (size: int)
requires 1 <= r <= n && 1 <= c <= m
requires n >= 3 && m >= 3
requires |grid| == n + 1
requires forall i :: 1 <= i <= n ==> |grid[i]| == m
requires forall i, j :: 1 <= i <= n && 1 <= j <= m ==> grid[i][j-1] in {'*', '.'}
{
    if grid[r][c-1] == '.' then 0
    else if grid[r][c-1] == '*' then
        var max_s := 0;
        var s := 1;
        while true
            invariant 0 <= s
            invariant forall k :: 0 <= k < s ==>
                (r - k >= 1 && r + k <= n && c - k >= 1 && c + k <= m &&
                 grid[r][c-1] == '*' && // Center
                 grid[r - k][c-1] == '*' && grid[r + k][c-1] == '*' && // Vertical
                 grid[r][c - k -1] == '*' && grid[r][c + k -1] == '*') // Horizontal
        {
            if r - s >= 1 && r + s <= n && c - s >= 1 && c + s <= m &&
               grid[r - s][c-1] == '*' && grid[r + s][c-1] == '*' &&
               grid[r][c - s -1] == '*' && grid[r][c + s -1] == '*'
            then
                max_s := s;
                s := s + 1;
            else
                return max_s;
        }
        max_s
    else 0
}

// Predicate to check if a grid cell (row, col) is covered by any of the given stars
predicate IsCovered(stars: seq<(int, int, int)>, r: int, c: int)
{
    exists S :: S in stars && StarCovers(S.0, S.1, S.2, r, c)
}

// A 2D array representation for the grid derived from the input string
type CharGrid = seq<seq<char>>
ghost function ParseGrid(input: string): (grid: CharGrid)
requires ValidInput(input)
ensures var lines := Split(input, '\n');
        var firstLine := Split(lines[0], ' ');
        var n := StringToInt(firstLine[0]);
        var m := StringToInt(firstLine[1]);
        |grid| == n + 1 &&
        (forall i :: 1 <= i <= n ==> |grid[i]| == m) &&
        (forall i, j :: 1 <= i <= n && 1 <= j <= m ==> grid[i][j-1] == lines[i][j-1])
{
    var lines := Split(input, '\n');
    var firstLine := Split(lines[0], ' ');
    var n := StringToInt(firstLine[0]);
    var m := StringToInt(firstLine[1]);
    var parsedGrid: seq<seq<char>> := new seq<seq<char>>(n + 1, i => new seq<char>(0, j => ' '));
    for r := 1 to n
        invariant 1 <= r <= n + 1
        invariant forall i :: 1 <= i < r ==> |parsedGrid[i]| == m
        invariant forall i, j :: 1 <= i < r && 1 <= j <= m ==> parsedGrid[i][j-1] == lines[i][j-1]
    {
        parsedGrid[r] := new seq<char>(m, c => lines[r][c]);
    }
    parsedGrid
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

    var grid := ParseGrid(input);
    var stars: seq<(int, int, int)> := [];
    
    // Create a mutable copy of the grid for marking covered cells
    var marked_grid: array<array<char>> := new array<array<char>>(n + 1);
    for r := 1 to n {
        marked_grid[r] := new array<char>(m);
        for c := 0 to m - 1 {
            marked_grid[r][c] := grid[r][c];
        }
    }

    for r := 1 to n {
        for c := 1 to m {
            if marked_grid[r][c-1] == '*' {
                var s = MaxStarSize(grid, n, m, r, c);
                if s > 0 {
                    stars := stars + [(r, c, s)];
                    // Mark the covered '*' cells
                    for i_mark := 1 to n {
                        for j_mark := 1 to m {
                            if StarCovers(r, c, s, i_mark, j_mark) {
                                marked_grid[i_mark][j_mark-1] := '.';
                            }
                        }
                    }
                }
            }
        }
    }

    // Verify if all original '*' are covered and no '.' are covered
    for r := 1 to n {
        for c := 1 to m {
            if grid[r][c-1] == '*' && marked_grid[r][c-1] == '*' { // Check if any original '*' is NOT covered
                return "-1\n";
            }
             if grid[r][c-1] == '.' && marked_grid[r][c-1] == '.' { // Check if any original '.' is covered
                // This condition must hold true since we only mark '*' as '.'
            }
        }
    }
    
    // Check if the found stars exactly cover the original '*'
    var verification_grid: array<array<char>> := new array<array<char>>(n + 1);
    for r := 1 to n {
        verification_grid[r] := new array<char>(m);
        for c := 0 to m - 1 {
            verification_grid[r][c] := '.'; // Initialize with '.'
        }
    }
    
    for star_idx := 0 to |stars|-1 {
        var r := stars[star_idx].0;
        var c := stars[star_idx].1;
        var s := stars[star_idx].2;

        for i_ver := 1 to n {
            for j_ver := 1 to m {
                if StarCovers(r, c, s, i_ver, j_ver) {
                    verification_grid[i_ver][j_ver-1] := '*';
                }
            }
        }
    }
    
    for r := 1 to n {
        for c := 1 to m {
            if verification_grid[r][c-1] != grid[r][c-1] {
                // This means the stars don't perfectly match the original grid
                return "-1\n";
            }
        }
    }

    return FormatStarOutput(|stars|, stars);
}
// </vc-code>

