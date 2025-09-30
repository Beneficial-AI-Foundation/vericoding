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
    ensures exp == 0 ==> power(base, exp) == 1
    ensures exp > 0 ==> power(base, exp) == base * power(base, exp - 1)
    ensures base >= 0 && exp >= 0 ==> power(base, exp) >= 0
    ensures base == 2 && exp >= 0 ==> power(base, exp) >= 1
    ensures base == 2 && exp >= 1 ==> power(base, exp) >= 2
    ensures base == 2 && exp >= 2 ==> power(base, exp) >= exp + 1
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}

lemma power_2_properties(n: int)
    requires n >= 0
    ensures n >= 2 ==> power(2, n) >= n + 1
    ensures power(2, n) >= 1
{
    if n == 0 {
        assert power(2, 0) == 1;
    } else if n == 1 {
        assert power(2, 1) == 2;
    } else if n == 2 {
        assert power(2, 2) == 4;
        assert 4 >= 3;
    } else {
        power_2_properties(n - 1);
        assert power(2, n) == 2 * power(2, n - 1);
        assert power(2, n - 1) >= n;
        assert power(2, n) >= 2 * n;
        assert 2 * n >= n + 1;
    }
}

lemma count_valid_sets_nonnegative(grid: array2<int>)
    requires ValidGrid(grid)
    ensures count_valid_sets(grid) >= 0
{
    assert grid.Length0 > 0 && grid.Length1 > 0;
    assert grid.Length0 * grid.Length1 > 0;
    assert sum_row_contributions(grid) >= 0;
    assert sum_col_contributions(grid) >= 0;
}

function int_to_string(n: int): string
    ensures |int_to_string(n)| > 0
{
    if n < 0 then "-" + nat_to_string(-n)
    else nat_to_string(n)
}

function nat_to_string(n: nat): string
    ensures |nat_to_string(n)| > 0
{
    if n < 10 then [digit_to_char(n)]
    else nat_to_string(n / 10) + [digit_to_char(n % 10)]
}

function digit_to_char(d: nat): char
    requires d < 10
{
    '0' + d as char
}

method parse_grid(stdin_input: string) returns (grid: array2<int>)
    requires ValidInput(stdin_input)
    ensures ValidGrid(grid)
{
    var lines := split_lines(stdin_input);
    var rows := |lines|;
    assert rows > 0;
    var cols := |lines[0]|;
    
    if cols == 0 {
        // Handle edge case: ensure at least 1x1 grid
        grid := new int[1, 1];
        grid[0, 0] := 0;
        return;
    }
    
    grid := new int[rows, cols];
    assert grid.Length0 == rows > 0;
    assert grid.Length1 == cols > 0;
    
    var i := 0;
    while i < rows
        invariant 0 <= i <= rows
        invariant grid.Length0 == rows && grid.Length1 == cols
        invariant rows > 0 && cols > 0
        invariant forall i', j' :: 0 <= i' < i && 0 <= j' < cols ==> 
            grid[i', j'] == 0 || grid[i', j'] == 1
    {
        var j := 0;
        while j < cols
            invariant 0 <= j <= cols
            invariant forall j' :: 0 <= j' < j ==> grid[i, j'] == 0 || grid[i, j'] == 1
            invariant forall i', j' :: 0 <= i' < i && 0 <= j' < cols ==> 
                grid[i', j'] == 0 || grid[i', j'] == 1
        {
            if j < |lines[i]| && lines[i][j] == '1' {
                grid[i, j] := 1;
            } else {
                grid[i, j] := 0;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

function split_lines(s: string): seq<string>
    ensures |split_lines(s)| > 0
{
    split_lines_helper(s, 0, 0)
}

function split_lines_helper(s: string, start: int, i: int): seq<string>
    requires 0 <= start <= i <= |s|
    ensures |split_lines_helper(s, start, i)| > 0
    decreases |s| - i
{
    if i == |s| then
        [s[start..i]]
    else if s[i] == '\n' then
        [s[start..i]] + split_lines_helper(s, i + 1, i + 1)
    else
        split_lines_helper(s, start, i + 1)
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
    var grid := parse_grid(stdin_input);
    count_valid_sets_nonnegative(grid);
    var count := count_valid_sets(grid);
    result := int_to_string(count) + "\n";
}
// </vc-code>

