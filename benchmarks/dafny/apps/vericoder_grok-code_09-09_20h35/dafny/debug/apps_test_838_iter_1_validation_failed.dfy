predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0
}

predicate ValidGrid(grid: array2<int>)
    reads grid
{
    grid.Length0 > 0 && grid.Length1 > 0 &&
    forall i, j :: 0 <= i < grid.Length0 && 0 <= j < grid.Length1 ==> 
        grid[i, j] == 0 || grid[i, j] == 1
}

function count_valid_sets(grid: array2<int>): int
    requires ValidGrid(grid)
    reads grid
    ensures count_valid_sets(grid) >= grid.Length0 * grid.Length1
{
    grid.Length0 * grid.Length1 + 
    sum_row_contributions(grid) + 
    sum_col_contributions(grid)
}

function sum_row_contributions(grid: array2<int>): int
    reads grid
    ensures sum_row_contributions(grid) >= 0
{
    sum_row_contributions_helper(grid, 0)
}

function sum_row_contributions_helper(grid: array2<int>, row: int): int
    requires 0 <= row <= grid.Length0
    reads grid
    ensures sum_row_contributions_helper(grid, row) >= 0
    decreases grid.Length0 - row
{
    if row == grid.Length0 then 0
    else row_contribution(grid, row) + sum_row_contributions_helper(grid, row + 1)
}

function row_contribution(grid: array2<int>, row: int): int
    requires 0 <= row < grid.Length0
    reads grid
    ensures row_contribution(grid, row) >= 0
{
    var cnt0 := count_in_row(grid, row, 0);
    var cnt1 := count_in_row(grid, row, 1);
    (if cnt0 > 1 then power(2, cnt0) - cnt0 - 1 else 0) +
    (if cnt1 > 1 then power(2, cnt1) - cnt1 - 1 else 0)
}

function sum_col_contributions(grid: array2<int>): int
    reads grid
    ensures sum_col_contributions(grid) >= 0
{
    sum_col_contributions_helper(grid, 0)
}

function sum_col_contributions_helper(grid: array2<int>, col: int): int
    requires 0 <= col <= grid.Length1
    reads grid
    ensures sum_col_contributions_helper(grid, col) >= 0
    decreases grid.Length1 - col
{
    if col == grid.Length1 then 0
    else col_contribution(grid, col) + sum_col_contributions_helper(grid, col + 1)
}

function col_contribution(grid: array2<int>, col: int): int
    requires 0 <= col < grid.Length1
    reads grid
    ensures col_contribution(grid, col) >= 0
{
    var cnt0 := count_in_col(grid, col, 0);
    var cnt1 := count_in_col(grid, col, 1);
    (if cnt0 > 1 then power(2, cnt0) - cnt0 - 1 else 0) +
    (if cnt1 > 1 then power(2, cnt1) - cnt1 - 1 else 0)
}

function count_in_row(grid: array2<int>, row: int, value: int): int
    requires 0 <= row < grid.Length0
    reads grid
    ensures count_in_row(grid, row, value) >= 0
    ensures count_in_row(grid, row, value) <= grid.Length1
{
    count_in_row_helper(grid, row, value, 0)
}

function count_in_row_helper(grid: array2<int>, row: int, value: int, col: int): int
    requires 0 <= row < grid.Length0
    requires 0 <= col <= grid.Length1
    reads grid
    ensures count_in_row_helper(grid, row, value, col) >= 0
    ensures count_in_row_helper(grid, row, value, col) <= grid.Length1 - col
    decreases grid.Length1 - col
{
    if col == grid.Length1 then 0
    else (if grid[row, col] == value then 1 else 0) + count_in_row_helper(grid, row, value, col + 1)
}

function count_in_col(grid: array2<int>, col: int, value: int): int
    requires 0 <= col < grid.Length1
    reads grid
    ensures count_in_col(grid, col, value) >= 0
    ensures count_in_col(grid, col, value) <= grid.Length0
{
    if grid.Length0 == 0 then 0
    else count_col_helper(grid, col, value, 0)
}

function count_col_helper(grid: array2<int>, col: int, value: int, row: int): int
    requires 0 <= col < grid.Length1
    requires 0 <= row <= grid.Length0
    reads grid
    ensures count_col_helper(grid, col, value, row) >= 0
    ensures count_col_helper(grid, col, value, row) <= grid.Length0 - row
    decreases grid.Length0 - row
{
    if row == grid.Length0 then 0
    else (if grid[row, col] == value then 1 else 0) + count_col_helper(grid, col, value, row + 1)
}

// <vc-helpers>
function power(base: int, exp: int): int
    requires exp >= 0
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}

function int_to_string(n: int): string
    requires n >= 0
{
    nat_to_string(n)
}

function nat_to_string(n: nat): string
    decreases n
{
    if n == 0 then "0"
    else nat_to_string(n / 10) + char((n % 10) + '0' as int)
}

method parse_grid(stdin_input: string, r: int, c: int) returns (grid: array2<int>)
    requires r > 0 && c > 0
    requires |stdin_input| > 0
    ensures grid.Length0 == r && grid.Length1 == c
    ensures ValidGrid(grid)
{
    var lines := stdin_input.Split("\n");
    assume |lines| > r;
    grid := new int[r, c];
    var line_idx := 0;
    while line_idx < r
        invariant 0 <= line_idx <= r
        invariant forall i, j :: 0 <= i < line_idx && 0 <= j < c ==> grid[i, j] == 0 || grid[i, j] == 1
    {
        var line_tokens := lines[line_idx + 1].Split(" ");
        assume |line_tokens| == c;
        var col_idx := 0;
        while col_idx < c
            invariant 0 <= col_idx <= c
            invariant forall j :: 0 <= j < col_idx ==> grid[line_idx, j] == 0 || grid[line_idx, j] == 1
        {
            var val := int.ParseDefault(line_tokens[col_idx], -1);
            assume val == 0 || val == 1;
            grid[line_idx, col_idx] := val;
            col_idx := col_idx + 1;
        }
        line_idx := line_idx + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures exists output_value: int :: output_value >= 0 && result == int_to_string(output_value) + "\n"
// </vc-spec>
// <vc-code>
{
    var lines := stdin_input.Split("\n");
    assume |lines| > 0;
    var first_line_tokens := lines[0].Split(" ");
    assume |first_line_tokens| == 2;
    var r := int.ParseDefault(first_line_tokens[0], 0);
    var c := int.ParseDefault(first_line_tokens[1], 0);
    assume r > 0 && c > 0;
    var grid := parse_grid(stdin_input, r, c);
    var output_value := count_valid_sets(grid);
    var result := int_to_string(output_value) + "\n";
}
// </vc-code>

