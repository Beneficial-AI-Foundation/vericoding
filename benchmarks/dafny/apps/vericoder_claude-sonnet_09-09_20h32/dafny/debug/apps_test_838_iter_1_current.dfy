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
    requires base >= 0 && exp >= 0
    ensures power(base, exp) >= 1
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}

function int_to_string(n: int): string
    requires n >= 0
    ensures |int_to_string(n)| > 0
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else int_to_string(n / 10) + int_to_string(n % 10)
}

function parse_lines(input: string): seq<string>
    ensures |parse_lines(input)| >= 0
{
    split_by_newline(input, 0, [])
}

function split_by_newline(input: string, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |input|
    ensures |split_by_newline(input, start, acc)| >= |acc|
    decreases |input| - start
{
    if start >= |input| then
        if start > 0 && input[start-1] != '\n' then acc + [input[start..]]
        else acc
    else
        var next_newline := find_next_newline(input, start);
        if next_newline == -1 then
            acc + [input[start..]]
        else
            split_by_newline(input, next_newline + 1, acc + [input[start..next_newline]])
}

function find_next_newline(input: string, start: int): int
    requires 0 <= start <= |input|
    ensures find_next_newline(input, start) == -1 || (start <= find_next_newline(input, start) < |input|)
    decreases |input| - start
{
    if start >= |input| then -1
    else if input[start] == '\n' then start
    else find_next_newline(input, start + 1)
}

function char_to_int(c: char): int
{
    if '0' <= c <= '9' then (c as int) - ('0' as int) else 0
}

function parse_grid_from_lines(lines: seq<string>) : (grid: array2<int>)
    requires |lines| > 0
    requires forall i :: 0 <= i < |lines| ==> |lines[i]| > 0
    ensures ValidGrid(grid)
    ensures fresh(grid)
{
    var rows := |lines|;
    var cols := |lines[0]|;
    var grid := new int[rows, cols];
    
    forall i, j | 0 <= i < rows && 0 <= j < cols && j < |lines[i]|
    {
        grid[i, j] := char_to_int(lines[i][j]);
    }
    
    grid
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
    var lines := parse_lines(stdin_input);
    if |lines| == 0 || |lines[0]| == 0 {
        return "0\n";
    }
    
    var grid := parse_grid_from_lines(lines);
    var count := count_valid_sets(grid);
    result := int_to_string(count) + "\n";
}
// </vc-code>

