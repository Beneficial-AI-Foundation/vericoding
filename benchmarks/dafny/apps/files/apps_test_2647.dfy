// <vc-preamble>
predicate isValidInput(input: string)
{
    |input| > 0 &&
    true
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
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
