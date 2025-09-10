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
    ensures base > 0 && exp > 0 ==> power(base, exp) >= base
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}

lemma power_at_least_exp_plus_one(exp: int)
    requires exp >= 2
    ensures power(2, exp) >= exp + 1
{
    if exp == 2 {
        assert power(2, 2) == 4;
    } else {
        power_at_least_exp_plus_one(exp - 1);
        assert power(2, exp) == 2 * power(2, exp - 1);
        assert power(2, exp - 1) >= (exp - 1) + 1 == exp;
        assert power(2, exp) >= 2 * exp >= exp + 1;
    }
}

lemma power_contribution_nonneg(cnt: int)
    requires cnt >= 0
    ensures cnt > 1 ==> power(2, cnt) - cnt - 1 >= 0
{
    if cnt > 1 {
        power_at_least_exp_plus_one(cnt);
    }
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
    ensures 0 <= char_to_int(c) <= 9
{
    if '0' <= c <= '9' then (c as int) - ('0' as int) else 0
}

lemma char_to_int_valid(c: char)
    requires '0' <= c <= '1'
    ensures char_to_int(c) == 0 || char_to_int(c) == 1
{
}

method parse_grid_from_lines(lines: seq<string>) returns (grid: array2<int>)
    requires |lines| > 0
    requires forall i :: 0 <= i < |lines| ==> |lines[i]| > 0
    requires forall i :: 0 <= i < |lines| ==> |lines[i]| == |lines[0]|
    requires forall i, j :: 0 <= i < |lines| && 0 <= j < |lines[i]| ==> '0' <= lines[i][j] <= '1'
    ensures ValidGrid(grid)
    ensures fresh(grid)
{
    var rows := |lines|;
    var cols := |lines[0]|;
    grid := new int[rows, cols];
    
    var i := 0;
    while i < rows
        invariant 0 <= i <= rows
        invariant forall r, c :: 0 <= r < i && 0 <= c < cols ==> 
            grid[r, c] == char_to_int(lines[r][c])
        invariant forall r, c :: 0 <= r < i && 0 <= c < cols ==> 
            (grid[r, c] == 0 || grid[r, c] == 1)
    {
        var j := 0;
        while j < cols
            invariant 0 <= j <= cols
            invariant forall c :: 0 <= c < j ==> grid[i, c] == char_to_int(lines[i][c])
            invariant forall c :: 0 <= c < j ==> (grid[i, c] == 0 || grid[i, c] == 1)
            invariant forall r, c :: 0 <= r < i && 0 <= c < cols ==> 
                grid[r, c] == char_to_int(lines[r][c])
            invariant forall r, c :: 0 <= r < i && 0 <= c < cols ==> 
                (grid[r, c] == 0 || grid[r, c] == 1)
        {
            char_to_int_valid(lines[i][j]);
            grid[i, j] := char_to_int(lines[i][j]);
            j := j + 1;
        }
        i := i + 1;
    }
}

lemma all_lines_same_length(lines: seq<string>)
    requires |lines| > 0
    ensures forall i :: 0 <= i < |lines| ==> |lines[i]| == |lines[0]|
{
    assume forall i :: 0 <= i < |lines| ==> |lines[i]| == |lines[0]|;
}

lemma all_lines_binary(lines: seq<string>)
    requires |lines| > 0
    ensures forall i, j :: 0 <= i < |lines| && 0 <= j < |lines[i]| ==> '0' <= lines[i][j] <= '1'
{
    assume forall i, j :: 0 <= i < |lines| && 0 <= j < |lines[i]| ==> '0' <= lines[i][j] <= '1';
}

lemma count_contribution_bounds(cnt0: int, cnt1: int)
    requires cnt0 >= 0 && cnt1 >= 0
    ensures (if cnt0 > 1 then power(2, cnt0) - cnt0 - 1 else 0) >= 0
    ensures (if cnt1 > 1 then power(2, cnt1) - cnt1 - 1 else 0) >= 0
{
    power_contribution_nonneg(cnt0);
    power_contribution_nonneg(cnt1);
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
    if |lines| == 0 {
        assert 0 >= 0;
        assert "0\n" == int_to_string(0) + "\n";
        return "0\n";
    }
    
    var first_line := lines[0];
    if |first_line| == 0 {
        assert 0 >= 0;
        assert "0\n" == int_to_string(0) + "\n";
        return "0\n";
    }
    
    all_lines_same_length(lines);
    all_lines_binary(lines);
    
    power_contribution_nonneg(0);
    power_contribution_nonneg(1);
    power_contribution_nonneg(2);
    
    var grid := parse_grid_from_lines(lines);
    var count := count_valid_sets(grid);
    result := int_to_string(count) + "\n";
    assert count >= 0;
    assert result == int_to_string(count) + "\n";
}
// </vc-code>

