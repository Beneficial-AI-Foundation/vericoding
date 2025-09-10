predicate isValidInput(input: string)
{
    |input| > 0 &&
    true // Simplified for placeholder
}

predicate isValidOutput(output: string)
{
    |output| > 0 &&
    (output == "-1\n" || 
     (output != "-1\n" && |output| > 1 && output[|output|-1] == '\n'))
}

datatype GridData = GridData(h: int, w: int, cells: seq<seq<char>>)

predicate validGrid(grid: GridData)
{
    grid.h > 0 && grid.w > 0 && 
    |grid.cells| == grid.h &&
    (forall i :: 0 <= i < grid.h ==> |grid.cells[i]| == grid.w) &&
    (forall i, j :: 0 <= i < grid.h && 0 <= j < grid.w ==> 
        grid.cells[i][j] == '.' || grid.cells[i][j] == '#') &&
    grid.cells[0][0] == '.' && grid.cells[grid.h-1][grid.w-1] == '.'
}

function parseInput(input: string): GridData
    requires isValidInput(input)
    ensures validGrid(parseInput(input))
{
    GridData(1, 1, [['.']])
}

predicate pathExists(grid: GridData)
    requires validGrid(grid)
{
    true
}

function maxChangeableWhiteCells(grid: GridData): int
    requires validGrid(grid)
    requires pathExists(grid)
    ensures 0 <= maxChangeableWhiteCells(grid) <= countWhiteCells(grid) - 2
    ensures maxChangeableWhiteCells(grid) == countWhiteCells(grid) - minCutSize(grid)
{
    0
}

function countWhiteCells(grid: GridData): int
    requires validGrid(grid)
    ensures countWhiteCells(grid) >= 2
{
    2
}

function minCutSize(grid: GridData): int
    requires validGrid(grid)
    requires pathExists(grid)
    ensures minCutSize(grid) >= 2
    ensures minCutSize(grid) <= countWhiteCells(grid)
{
    2
}

// <vc-helpers>
lemma PathExistsLemma(grid: GridData)
    requires validGrid(grid)
    ensures pathExists(grid) <==> true
{
}

lemma MinCutSizeLemma(grid: GridData)
    requires validGrid(grid)
    requires pathExists(grid)
    ensures minCutSize(grid) == 2
{
}

function intToString(n: int): string
    decreases if n < 0 then -n else n + 1
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToString(-n)
    else var d := n % 10; var rest := n / 10;
        (if rest > 0 then intToString(rest) else "") + 
        (if d == 0 then "0" else if d == 1 then "1" else if d == 2 then "2" else if d == 3 then "3" 
         else if d == 4 then "4" else if d == 5 then "5" else if d == 6 then "6" else if d == 7 then "7"
         else if d == 8 then "8" else "9")
}

lemma IntToStringLemma(n: int)
    decreases if n < 0 then -n else n + 1
    ensures |intToString(n)| >= 1
    ensures n >= 0 ==> intToString(n) != "-" + intToString(0)
{
    if n < 0 {
        IntToStringLemma(-n);
    } else if n > 0 {
        var rest := n / 10;
        if rest > 0 {
            IntToStringLemma(rest);
        }
        assert n == rest * 10 + (n % 10);
        var s := intToString(n);
        var s_rest := if rest > 0 then intToString(rest) else "";
        var s_digit := if (n % 10) == 0 then "0" else if (n % 10) == 1 then "1" else if (n % 10) == 2 then "2" else if (n % 10) == 3 then "3" 
                      else if (n % 10) == 4 then "4" else if (n % 10) == 5 then "5" else if (n % 10) == 6 then "6" else if (n % 10) == 7 then "7"
                      else if (n % 10) == 8 then "8" else "9";
        assert s == s_rest + s_digit;
        assert s_rest != "-" + intToString(0);
        assert |s_rest| >= 0;
        assert s_digit != "";
        assert s != "-" + intToString(0);
    }
}

lemma IntToStringPositive(n: int)
    requires n >= 0
    ensures intToString(n) != "-" + intToString(0)
{
    if n == 0 {
        assert intToString(0) == "0";
        assert "-" + intToString(0) == "-0";
        assert "0" != "-0";
    } else {
        IntToStringLemma(n);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires |stdin_input| > 0
    requires isValidInput(stdin_input)
    ensures isValidOutput(output)
    ensures output == "-1\n" || 
            (exists result: int :: result >= 0 && output == intToString(result) + "\n")
    ensures output == "-1\n" <==> !pathExists(parseInput(stdin_input))
    ensures output != "-1\n" ==> 
            (exists result: int, grid: GridData :: 
                grid == parseInput(stdin_input) &&
                result == maxChangeableWhiteCells(grid) &&
                output == intToString(result) + "\n")
// </vc-spec>
// <vc-code>
{
    var grid := parseInput(stdin_input);
    PathExistsLemma(grid);
    
    if !pathExists(grid) {
        output := "-1\n";
    } else {
        var result := maxChangeableWhiteCells(grid);
        IntToStringPositive(result);
        output := intToString(result) + "\n";
    }
}
// </vc-code>

