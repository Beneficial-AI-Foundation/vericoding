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
function intToString(n: int): string
    requires n >= 0
    ensures |intToString(n)| > 0
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else intToString(n / 10) + intToString(n % 10)
}

lemma intToStringProperties(n: int)
    requires n >= 0
    ensures |intToString(n)| > 0
    ensures intToString(n) != "-1"
    ensures n > 0 ==> intToString(n)[0] != '-'
{
    if n == 0 {
        assert intToString(n) == "0";
        assert "0" != "-1";
    } else if n < 10 {
        assert intToString(n) == [('0' as int + n) as char];
        assert |intToString(n)| == 1;
        assert intToString(n)[0] == ('0' as int + n) as char;
        assert ('0' as int + n) as char != '-';
        assert intToString(n) != "-1";
    } else {
        intToStringProperties(n / 10);
        intToStringProperties(n % 10);
        assert n / 10 > 0;
        assert intToString(n / 10)[0] != '-';
        assert intToString(n) == intToString(n / 10) + intToString(n % 10);
        assert |intToString(n / 10)| > 0;
        assert intToString(n)[0] == intToString(n / 10)[0];
        assert intToString(n) != "-1";
    }
}

lemma outputValidityLemma(result: int)
    requires result >= 0
    ensures isValidOutput(intToString(result) + "\n")
    ensures |intToString(result) + "\n"| > 0
    ensures intToString(result) + "\n" != "-1\n"
    ensures |intToString(result) + "\n"| > 1
    ensures (intToString(result) + "\n")[|(intToString(result) + "\n")|-1] == '\n'
{
    intToStringProperties(result);
    var s := intToString(result) + "\n";
    assert |s| == |intToString(result)| + 1;
    assert |intToString(result)| > 0;
    assert |s| > 1;
    assert s[|s|-1] == '\n';
    assert intToString(result) != "-1";
    assert s != "-1\n";
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
        outputValidityLemma(result);
        output := intToString(result) + "\n";
    }
}
// </vc-code>

