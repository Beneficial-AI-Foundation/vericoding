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
function digit_char(d: int): char
  requires 0 <= d <= 9
{
  ('0' as int + d) as char
}

function int_to_string(n: nat): seq<char>
{
  if n == 0 then "0"
  else var q := n / 10;
       var r := n % 10;
       if q == 0 then [digit_char(r)]
       else int_to_string(q) + [digit_char(r)]
}

function power(base: int, exp: nat): int
  decreases exp
{
  if exp == 0 then 1 else base * power(base, exp - 1)
}

lemma power_greater_than_n_plus_1(n: nat)
  requires n >= 2
  ensures power(2, n) > n + 1
  decreases n
{
  if n == 2 {
    assert power(2, 2) == 4 > 3 == 2 + 1;
  } else {
    power_greater_than_n_plus_1(n - 1);
    assert power(2, n) == 2 * power(2, n - 1) > 2 * (n - 1 + 1) == 2 * n > n + 1;
  }
}

function row_contribution(grid: array2<int>, row: int): int
    requires 0 <= row < grid.Length0
    reads grid
    ensures row_contribution(grid, row) >= 0
{
    var cnt0 := count_in_row(grid, row, 0);
    var cnt1 := count_in_row(grid, row, 1);
    var res0 := if cnt0 > 1 then power(2, cnt0) - cnt0 - 1 else 0;
    var res1 := if cnt1 > 1 then power(2, cnt1) - cnt1 - 1 else 0;
    if cnt0 > 1 {
      power_greater_than_n_plus_1(cnt0);
      assert power(2, cnt0) > cnt0 + 1;
      assert res0 > 0;
    }
    if cnt1 > 1 {
      power_greater_than_n_plus_1(cnt1);
      assert power(2, cnt1) > cnt1 + 1;
      assert res1 > 0;
    }
    res0 + res1
}

function col_contribution(grid: array2<int>, col: int): int
    requires 0 <= col < grid.Length1
    reads grid
    ensures col_contribution(grid, col) >= 0
{
    var cnt0 := count_in_col(grid, col, 0);
    var cnt1 := count_in_col(grid, col, 1);
    var res0 := if cnt0 > 1 then power(2, cnt0) - cnt0 - 1 else 0;
    var res1 := if cnt1 > 1 then power(2, cnt1) - cnt1 - 1 else 0;
    if cnt0 > 1 {
      power_greater_than_n_plus_1(cnt0);
      assert power(2, cnt0) > cnt0 + 1;
      assert res0 > 0;
    }
    if cnt1 > 1 {
      power_greater_than_n_plus_1(cnt1);
      assert power(2, cnt1) > cnt1 + 1;
      assert res1 > 0;
    }
    res0 + res1
}

function find_first(s: seq<char>, ch: char): nat
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == ch then 0
  else 1 + find_first(s[1..], ch)
}

function split_on(s: seq<char>, ch: char): seq<seq<char>>
{
  if |s| == 0 then []
  else var pos := find_first(s, ch);
       if pos == |s| then [s]
       else [s[..pos]] + split_on(s[pos+1..], ch)
}

function split_lines(s: seq<char>): seq<seq<char>>
{
  split_on(s, '\n')
}

function split_spaces(s: seq<char>): seq<seq<char>>
{
  split_on(s, ' ')
}

function atoi(s: seq<char>): nat
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  var len := |s| - 1;
  if |s| == 1 then s[0] - ('0' as int)
  else (s[0] - ('0' as int)) * power(10, len) + atoi(s[1..])
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
  var lines := split_lines(stdin_input);
  var parts := split_spaces(lines[0]);
  var H := atoi(parts[0]);
  var W := atoi(parts[1]);
  var grid := new int[H, W];
  for i := 0 to H - 1
    invariant 0 <= i <= H
  {
    var row_str := lines[i + 1];
    for j := 0 to W - 1
      invariant 0 <= j <= W
    {
      grid[i, j] := row_str[j] - '0';
    }
  }
  var output_value := count_valid_sets(grid);
  result := int_to_string(output_value) + "\n";
}
// </vc-code>

