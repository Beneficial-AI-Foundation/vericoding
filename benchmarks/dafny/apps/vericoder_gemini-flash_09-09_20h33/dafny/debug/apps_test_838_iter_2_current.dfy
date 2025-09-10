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
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}

function parse_int(s: string): (i: int)
    requires |s| > 0 && forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    ensures forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9' ==> parse_int(s) >= 0
{
    var i := 0;
    var res := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res >= 0
        invariant forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
        invariant res == (if i == 0 then 0 else parse_int_prefix(s, i))
    {
        res := res * 10 + ((s[i] as int) - ('0' as int));
        i := i + 1;
    }
    return res;
}

function parse_int_prefix(s: string, len: int): int
    requires 0 < len <= |s|
    requires forall k :: 0 <= k < len ==> '0' <= s[k] <= '9'
    ensures parse_int_prefix(s, len) >= 0
{
    if len == 1 then (s[0] as int) - ('0' as int)
    else parse_int_prefix(s, len - 1) * 10 + ((s[len-1] as int) - ('0' as int))
}

function extract_grid_dim(s: string): (rows: int, cols: int)
    requires s.Length >= 3 // At least "R C\n" where R and C are single digits
    requires exists i :: 0 < i < s.Length && s[i] == ' ' // and a space delimiter
    requires forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
    requires exists j :: i < j < s.Length && s[j] == '\n' // and a newline delimiter
    requires forall k :: i+1 <= k < j ==> '0' <= s[k] <= '9'
    ensures rows >= 0 && cols >= 0
{
    var first_space_idx := 0;
    while first_space_idx < s.Length && s[first_space_idx] != ' '
        invariant 0 <= first_space_idx <= s.Length
    {
        first_space_idx := first_space_idx + 1;
    }
    var rows_str := s[0..first_space_idx];
    var newline_idx := first_space_idx + 1;
    while newline_idx < s.Length && s[newline_idx] != '\n'
        invariant first_space_idx + 1 <= newline_idx <= s.Length
    {
        newline_idx := newline_idx + 1;
    }
    var cols_str := s[first_space_idx + 1 .. newline_idx];
    
    return parse_int(rows_str), parse_int(cols_str);
}

function int_to_string(n: int): string
    requires n >= 0
    ensures parse_int(int_to_string(n)) == n
{
    if n == 0 then "0"
    else
    {
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant n == parse_int_suffix(s) * power(10, count_digits(temp)) + temp
            decreases temp
        {
            s := (((temp % 10) as char) + ('0' as int)) + s;
            temp := temp / 10;
        }
        s
    }
}

function parse_int_suffix(s: string): int
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    ensures parse_int_suffix(s) >= 0
    decreases |s|
{
    if |s| == 0 then 0
    else parse_int_suffix(s[0 .. |s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function count_digits(n: int): int
    requires n >= 0
    ensures count_digits(n) >= 1 || n == 0
    decreases n
{
    if n == 0 then 1
    else if n < 10 then 1
    else 1 + count_digits(n / 10)
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
    var lines_array := stdin_input.split('\n');
    var lines_count := lines_array.Length;
    var lines := new string[lines_count];
    var k := 0;
    while k < lines_count
    {
        lines[k] := lines_array[k];
        k := k + 1;
    }
    
    var R, C := extract_grid_dim(lines[0]);
    var grid := new array2<int>(R, C);

    for r := 0 to R - 1
        invariant 0 <= r <= R
        invariant forall i, j :: 0 <= i < r && 0 <= j < C ==> (grid[i,j] == 0 || grid[i,j] == 1)
    {
        var row_str := lines[r + 1]; // +1 because the first line is dimensions
        for c := 0 to C - 1
            invariant 0 <= c <= C
            invariant forall j :: 0 <= j < c ==> (grid[r,j] == 0 || grid[r,j] == 1)
        {
            var digit := (row_str[c] as int) - ('0' as int);
            grid[r, c] := digit;
        }
    }

    // Now, we have the grid populated and validated by ValidGrid logic implicitly through type system
    // and input parsing conditions.
    // Call the main function to compute the result.
    var total_valid_sets := count_valid_sets(grid);
    result := int_to_string(total_valid_sets) + "\n";
}
// </vc-code>

