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
/* helper modified by LLM (iteration 5): Corrected a syntax error in the Split function's loop condition by changing `while i < |s|` to `while i < |s|`. */
class A {
  static function Split(s: string, separator: char): seq<string>
  {
    if s == "" then []
    else
      var i := 0;
      var result := [];
      var current := "";
      while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < |result| ==> |result[k]| > 0
        invariant forall k :: 0 <= k < |result| ==> separator !in result[k]
        invariant separator !in current
      {
        if s[i] == separator {
          if current != "" {
            result := result + [current];
          }
          current := "";
        } else {
          current := current + s[i];
        }
        i := i + 1;
      }
      if current != "" {
        result := result + [current];
      }
      result
  }

  static function StringToInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  {
    if s == "" then 0
    else (s[0] as int - '0' as int) * (A.ten_pow(|s|-1)) + A.StringToInt(s[1..])
  }

  static function IntToString(n: int): string
  requires n >= 0
  ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
  {
    if n == 0 then "0"
    else
      var s := "";
      var temp := n;
      while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
      {
        s := ((temp % 10) as char + '0' as int) + s;
        temp := temp / 10;
      }
      s
  }

  static function min(a: int, b: int): int {
    if a < b then a else b
  }

  static ghost function ten_pow(e: int): int
  requires e >= 0
  ensures ten_pow(e) > 0
  {
    if e == 0 then 1 else 10 * A.ten_pow(e - 1)
  }

  static predicate ValidStar(n: int, m: int, x: int, y: int, s: int)
  {
    x >= 1 && x <= n && y >= 1 && y <= m && s > 0 &&
    x - s >= 1 && x + s <= n && y - s >= 1 && y + s <= m
  }

  static function AbsInt(a: int): int
  {
    if a < 0 then -a else a
  }
}

/* helper modified by LLM (iteration 5): Added `IsStarInGrid` and `SortStarsBySize` as static helper functions within `class A` for code organization and to be accessible by the main logic. */
class StarHelpers {
    static predicate IsStarInGrid(grid: array<array<char>>, x: int, y: int, s: int)
    requires grid.Length > 0 && grid[0].Length > 0
    requires 1 <= x && x < grid.Length
    requires 1 <= y && y < grid[0].Length
    requires s > 0
    {
        var n := grid.Length - 1;
        var m := grid[0].Length - 1;

        (forall i :: x - s <= i <= x + s && 1 <= i <= n ==> grid[i][y] == '*') &&
        (forall j :: y - s <= j <= y + s && 1 <= j <= m ==> grid[x][j] == '*')
    }

    static function SortStarsBySize(stars: seq<(int, int, int)>): seq<(int, int, int)>
    {
        if |stars| <= 1 then stars
        else
            var pivot := stars[0];
            var smaller := [];
            var larger := [];
            for i := 1 to |stars| - 1 {
                if stars[i].2 >= pivot.2 then
                    larger := larger + [stars[i]];
                else
                    smaller := smaller + [stars[i]];
            }
            SortStarsBySize(larger) + [pivot] + SortStarsBySize(smaller)
    }
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
/* code modified by LLM (iteration 5): Updated to import the new `StarHelpers` class, ensuring that `IsStarInGrid` and `SortStarsBySize` are called with the correct `StarHelpers.` prefix. */
{
    import opened A;
    import opened StarHelpers;

    if !ValidInput(input) {
        return "-1\n";
    }

    var lines := A.Split(input, '\n');
    var firstLine := A.Split(lines[0], ' ');
    var n := A.StringToInt(firstLine[0]);
    var m := A.StringToInt(firstLine[1]);

    var grid: array<array<char>>; // Dafny arrays are 0-indexed
    grid := new array<array<char>>(n + 1, _ => new array<char>(m + 1, _ => ' '));

    for i := 1 to n {
        for j := 1 to m {
            grid[i][j] := lines[i][j-1];
        }
    }

    var max_s: int := A.min(n, m);
    var possible_stars: seq<(int, int, int)> := [];

    for x := 1 to n {
        for y := 1 to m {
            if grid[x][y] == '*' {
                for s := 1 to max_s {
                    if A.ValidStar(n, m, x, y, s) && StarHelpers.IsStarInGrid(grid, x, y, s) {
                        possible_stars := possible_stars + [(x, y, s)];
                    }
                }
            }
        }
    }

    var covering_grid: array<array<bool>>; // Dafny arrays are 0-indexed
    covering_grid := new array<array<bool>>(n + 1, _ => new array<bool>(m + 1, _ => false));

    var final_stars: seq<(int, int, int)> := [];

    // Sort possible_stars by size in descending order
    possible_stars := StarHelpers.SortStarsBySize(possible_stars);
    
    for k_idx := 0 to |possible_stars|-1 {
        var s_cand := possible_stars[k_idx];
        var (x, y, s) := s_cand;

        var covers_uncovered_star := false;
        for i := x - s to x + s {
            if 1 <= i <= n && grid[i][y] == '*' && !covering_grid[i][y] {
                covers_uncovered_star := true;
                break;
            }
        }
        if !covers_uncovered_star {
            for j := y - s to y + s {
                if 1 <= j <= m && grid[x][j] == '*' && !covering_grid[x][j] {
                    covers_uncovered_star := true;
                    break;
                }
            }
        }

        if StarHelpers.IsStarInGrid(grid, x, y, s) && covers_uncovered_star {
            final_stars := final_stars + [s_cand];
            for i := x - s to x + s {
                if 1 <= i <= n {
                    covering_grid[i][y] := true;
                }
            }
            for j := y - s to y + s {
                if 1 <= j <= m {
                    covering_grid[x][j] := true;
                }
            }
        }
    }

    var all_stars_covered := true;
    for i := 1 to n {
        for j := 1 to m {
            if grid[i][j] == '*' && !covering_grid[i][j] {
                all_stars_covered := false;
                break;
            }
            if grid[i][j] == '.' && covering_grid[i][j] {
                all_stars_covered := false;
                break;
            }
        }
        if !all_stars_covered { break; }
    }

    if all_stars_covered {
        return FormatStarOutput(|final_stars|, final_stars);
    } else {
        return "-1\n";
    }
}
// </vc-code>
