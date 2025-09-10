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
function parse_int_list(s: string, start: int): (result: seq<int>, end_index: int)
  requires 0 <= start <= |s|
  ensures |result| >= 0
  ensures start <= end_index <= |s|
  decreases |s| - start
{
  if start == |s| then ([], start)
  else if s[start] == ' ' || s[start] == '\n' then parse_int_list(s, start + 1)
  else
    var (num, end_idx) := parse_number(s, start);
    var (rest, final_idx) := parse_int_list(s, end_idx);
    ([num] + rest, final_idx)
}

function parse_number(s: string, start: int): (num: int, end_index: int)
  requires 0 <= start < |s|
  requires '0' as int <= s[start] as int <= '9' as int
  ensures start < end_index <= |s|
  decreases |s| - start
{
  if start == |s| || s[start] as int < '0' as int || s[start] as int > '9' as int then (0, start)
  else
    var digit := s[start] as int - '0' as int;
    var (rest_num, end_idx) := parse_number(s, start + 1);
    (digit * power(10, |s| - start - 1) + rest_num, end_idx)
}

function parse_grid(stdin_input: string): array2<int>
  requires ValidInput(stdin_input)
  ensures ValidGrid(parse_grid(stdin_input))
{
  var lines := split_lines(stdin_input);
  var rows := |lines|;
  var cols := if rows > 0 then count_numbers(lines[0]) else 0;
  var grid := new int[rows, cols]; // Fixed array2 initialization
  
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant forall r, c :: 0 <= r < i && 0 <= c < cols ==> grid[r, c] == 0 || grid[r, c] == 1
  {
    var numbers := parse_line(lines[i]);
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant forall c :: 0 <= c < j ==> grid[i, c] == 0 || grid[i, c] == 1
    {
      grid[i, j] := numbers[j];
      j := j + 1;
    }
    i := i + 1;
  }
  grid
}

function split_lines(s: string): seq<string>
  ensures |split_lines(s)| >= 1
{
  split_lines_helper(s, 0)
}

function split_lines_helper(s: string, start: int): seq<string>
  requires 0 <= start <= |s|
  decreases |s| - start
{
  if start == |s| then [""]
  else if s[start] == '\n' then [""] + split_lines_helper(s, start + 1)
  else
    var line_end := find_next_newline(s, start);
    var line := s[start..line_end];
    var rest := split_lines_helper(s, line_end + 1);
    [line] + rest
}

function find_next_newline(s: string, start: int): int
  requires 0 <= start <= |s|
  ensures start <= find_next_newline(s, start) <= |s|
  decreases |s| - start
{
  if start == |s| || s[start] == '\n' then start
  else find_next_newline(s, start + 1)
}

function count_numbers(line: string): int
{
  count_numbers_helper(line, 0, false)
}

function count_numbers_helper(line: string, pos: int, in_number: bool): int
  requires 0 <= pos <= |line|
  decreases |line| - pos
{
  if pos == |line| then (if in_number then 1 else 0)
  else if line[pos] == ' ' then
    (if in_number then 1 else 0) + count_numbers_helper(line, pos + 1, false)
  else
    count_numbers_helper(line, pos + 1, true)
}

function parse_line(line: string): seq<int>
  ensures |parse_line(line)| == count_numbers(line)
{
  var (nums, _) := parse_int_list(line, 0);
  nums
}

function int_to_string(n: int): string
  ensures |int_to_string(n)| >= 1
{
  if n == 0 then "0"
  else if n < 0 then "-" + int_to_string_helper(-n)
  else int_to_string_helper(n)
}

function int_to_string_helper(n: int): string
  requires n > 0
  ensures |int_to_string_helper(n)| >= 1
{
  if n < 10 then [digit_to_char(n)]
  else int_to_string_helper(n / 10) + [digit_to_char(n % 10)]
}

function digit_to_char(d: int): char
  requires 0 <= d <= 9
{
  ('0' as int + d) as char
}

function power(base: int, exp: int): int
  requires exp >= 0
  ensures exp == 0 ==> power(base, exp) == 1
  ensures exp > 0 ==> power(base, exp) == base * power(base, exp - 1)
{
  if exp == 0 then 1 else base * power(base, exp - 1)
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
  var count := count_valid_sets(grid);
  result := int_to_string(count) + "\n";
}
// </vc-code>

