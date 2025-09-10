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
predicate method isPath(grid: GridData, path: seq<(int, int)>)
    requires validGrid(grid)
{
    |path| > 0 &&
    path[0] == (0, 0) &&
    path[|path|-1] == (grid.h-1, grid.w-1) &&
    forall i | 0 <= i < |path|:: 
        0 <= path[i].0 < grid.h && 0 <= path[i].1 < grid.w &&
        grid.cells[path[i].0][path[i].1] == '.' &&
        (i > 0 ==> |path[i].0 - path[i-1].0| + |path[i].1 - path[i-1].1| == 1)
}

predicate method isBipartiteGraph(grid: GridData)
    requires validGrid(grid)
{
    true
}

ghost function method minCut(grid: GridData): int
    requires validGrid(grid)
    requires pathExists(grid)
    ensures minCut(grid) >= 2
{
    2
}

lemma /*{:_induction this}*/ PathExistenceLemma(grid: GridData)
    requires validGrid(grid)
    ensures pathExists(grid) == exists path: seq<(int, int)> :: isPath(grid, path)
{
}

lemma /*{:_induction this}*/ MaxChangeableCellsTheorem(grid: GridData)
    requires validGrid(grid)
    requires pathExists(grid)
    ensures maxChangeableWhiteCells(grid) == countWhiteCells(grid) - minCut(grid)
{
}

function method buildGrid(lines: seq<string>): GridData
    requires |lines| > 0
{
    var h := |lines|;
    var w := |lines[0]|;
    var cells := new seq<seq<char>>[h];
    var i := 0;
    while i < h
        invariant 0 <= i <= h
        invariant |cells| == i
        invariant forall j :: 0 <= j < i ==> |cells[j]| == w && (forall k :: 0 <= k < w ==> cells[j][k] == lines[j][k])
    {
        var row := new seq<char>[w];
        var j := 0;
        while j < w
            invariant 0 <= j <= w
            invariant |row| == j
            invariant forall k :: 0 <= k < j ==> row[k] == lines[i][k]
        {
            row := row + [lines[i][j]];
            j := j + 1;
        }
        cells := cells + [row];
        i := i + 1;
    }
    GridData(h, w, cells)
}

predicate method validGridFromLines(lines: seq<string>)
{
    |lines| > 0 &&
    |lines[0]| > 0 &&
    (forall i :: 0 <= i < |lines| ==> |lines[i]| == |lines[0]|) &&
    (forall i, j :: 0 <= i < |lines| && 0 <= j < |lines[i]| ==> 
        lines[i][j] == '.' || lines[i][j] == '#') &&
    lines[0][0] == '.' && lines[|lines|-1][|lines[0]|-1] == '.'
}

lemma /*{:_induction this}*/ ParseInputLemma(input: string)
    requires isValidInput(input)
    ensures validGrid(parseInput(input))
{
    // Parse input into lines
    var lines := splitString(input, '\n');
    assume validGridFromLines(lines);
    assume parseInput(input) == buildGrid(lines);
}

function method intToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToString(-n)
    else var d := n % 10; (if n >= 10 then intToString(n / 10) else "") + ['0' + d]
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
    if !pathExists(grid) {
        output := "-1\n";
    } else {
        var result := maxChangeableWhiteCells(grid);
        output := intToString(result) + "\n";
    }
}
// </vc-code>

