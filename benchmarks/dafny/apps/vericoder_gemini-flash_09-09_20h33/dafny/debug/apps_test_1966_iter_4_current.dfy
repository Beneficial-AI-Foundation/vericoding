predicate contains_valid_input_format(input: string)
{
    exists n: int :: 1 <= n <= 100 && n % 2 == 1 && 
        input_has_correct_structure_for_n(input, n) &&
        input_contains_exactly_four_pieces_of_size_n(input, n) &&
        all_pieces_contain_only_binary_chars(input, n)
}

predicate input_has_correct_structure_for_n(input: string, n: int)
    requires 1 <= n <= 100 && n % 2 == 1
{
    var lines := split_by_newline(input);
    |lines| >= 4*n + 4 &&
    is_valid_integer_string(lines[0]) &&
    string_to_int(lines[0]) == n &&
    (|lines| > n+1 ==> lines[n+1] == "") && 
    (|lines| > 2*n+2 ==> lines[2*n+2] == "") && 
    (|lines| > 3*n+3 ==> lines[3*n+3] == "")
}

predicate input_contains_exactly_four_pieces_of_size_n(input: string, n: int)
    requires 1 <= n <= 100 && n % 2 == 1
{
    var lines := split_by_newline(input);
    |lines| >= 4*n + 4 &&
    (forall i | 1 <= i <= n && i < |lines| :: |lines[i]| == n) &&
    (forall i | n+2 <= i <= 2*n+1 && i < |lines| :: |lines[i]| == n) &&
    (forall i | 2*n+3 <= i <= 3*n+2 && i < |lines| :: |lines[i]| == n) &&
    (forall i | 3*n+4 <= i <= 4*n+3 && i < |lines| :: |lines[i]| == n)
}

predicate all_pieces_contain_only_binary_chars(input: string, n: int)
    requires 1 <= n <= 100 && n % 2 == 1
{
    var lines := split_by_newline(input);
    |lines| >= 4*n + 4 &&
    (forall i | 1 <= i <= n && i < |lines| :: 
        forall j | 0 <= j < |lines[i]| :: lines[i][j] == '0' || lines[i][j] == '1') &&
    (forall i | n+2 <= i <= 2*n+1 && i < |lines| :: 
        forall j | 0 <= j < |lines[i]| :: lines[i][j] == '0' || lines[i][j] == '1') &&
    (forall i | 2*n+3 <= i <= 3*n+2 && i < |lines| :: 
        forall j | 0 <= j < |lines[i]| :: lines[i][j] == '0' || lines[i][j] == '1') &&
    (forall i | 3*n+4 <= i <= 4*n+3 && i < |lines| :: 
        forall j | 0 <= j < |lines[i]| :: lines[i][j] == '0' || lines[i][j] == '1')
}

predicate is_valid_integer_string(s: string)
{
    |s| > 0 && 
    (s[0] != '0' || |s| == 1) &&
    forall i | 0 <= i < |s| :: '0' <= s[i] <= '9'
}

predicate represents_minimum_recoloring_count(input: string, output: string)
{
    is_valid_integer_string(output) &&
    contains_valid_input_format(input) &&
    var n := extract_n_from_input(input);
    var pieces := extract_pieces_from_input(input);
    |pieces| == 4 &&
    (forall piece | piece in pieces :: 
        |piece| == n && 
        (forall row | row in piece :: 
            |row| == n &&
            (forall i | 0 <= i < |row| :: row[i] == '0' || row[i] == '1'))) &&
    string_to_int(output) == minimum_recoloring_for_pieces(pieces, n)
}

function extract_n_from_input(input: string): int
    requires contains_valid_input_format(input)
    ensures 1 <= extract_n_from_input(input) <= 100
    ensures extract_n_from_input(input) % 2 == 1
{
    var lines := split_by_newline(input);
    if |lines| > 0 && is_valid_integer_string(lines[0]) then
        string_to_int(lines[0])
    else
        1
}

function extract_pieces_from_input(input: string): seq<seq<string>>
    requires contains_valid_input_format(input)
    ensures |extract_pieces_from_input(input)| == 4
{
    var lines := split_by_newline(input);
    var n := extract_n_from_input(input);
    [
        lines[1..n+1],
        lines[n+2..2*n+2], 
        lines[2*n+3..3*n+3],
        lines[3*n+4..4*n+4]
    ]
}

function minimum_recoloring_for_pieces(pieces: seq<seq<string>>, n: int): int
    requires |pieces| == 4
    requires n >= 1 && n % 2 == 1
    requires forall piece | piece in pieces :: 
             |piece| == n && 
             (forall row | row in piece :: 
                 |row| == n &&
                 (forall i | 0 <= i < |row| :: row[i] == '0' || row[i] == '1'))
    ensures 0 <= minimum_recoloring_for_pieces(pieces, n) <= 2*n*n
{
    0
}

// <vc-helpers>
function split_by_newline(s: string): seq<string>
  reads s
  ensures forall i | 0 <= i < |split_by_newline(s)| :: split_by_newline(s)[i] != "" ==> !split_by_newline(s)[i].Contains('\n')
{
  if s == "" then
    [""] // Return a sequence with an empty string for an empty input
  else
    var parts_list := List.CreateEmpty<string>();
    var current_index := 0;
    while current_index < |s|
      invariant 0 <= current_index <= |s|
      invariant parts_list != null
      invariant forall i | 0 <= i < |parts_list.Elements| :: (parts_list.Elements)[i] != "" ==> !(parts_list.Elements)[i].Contains('\n')
      decrease |s| - current_index
    {
      var newline_index := s.IndexOf('\n', current_index);
      if newline_index == -1
      {
        parts_list.Add(s.Substring(current_index));
        current_index := |s|;
      }
      else
      {
        parts_list.Add(s.Substring(current_index, newline_index - current_index));
        current_index := newline_index + 1;
      }
    }
    // Handle the case where the string ends with a newline
    if |s| > 0 && s[|s|-1] == '\n' then
      parts_list.Add("");
    parts_list.Elements
}

function string_to_int(s: string): int
  requires is_valid_integer_string(s)
  reads s
  ensures string_to_int(s) >= 0
{
  var n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n >= 0
  {
    n := n * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
  n
}

function calculate_recoloring_cost(piece_rows: seq<string>, n: int, target_char: char): int
  requires |piece_rows| == n
  requires forall row | row in piece_rows :: |row| == n && (forall i | 0 <= i < |row| :: row[i] == '0' || row[i] == '1')
  requires target_char == '0' || target_char == '1'
  ensures 0 <= calculate_recoloring_cost(piece_rows, n, target_char) <= n * n
{
  var cost := 0;
  for row_idx := 0 to n - 1
    invariant 0 <= row_idx <= n
    invariant 0 <= cost <= row_idx * n
    // The invariant for 'cost' should reflect the sum of mismatches encountered so far from processed rows.
    invariant cost == (sum r' | 0 <= r' < row_idx ::
                        (sum c' | 0 <= c' < n :: (if piece_rows[r'][c'] != target_char then 1 else 0)))
  {
    var row := piece_rows[row_idx];
    for col_idx := 0 to n - 1
      invariant 0 <= col_idx <= n
      invariant 0 <= cost <= row_idx * n + col_idx
      // This combined invariant needs to correctly reflect accumulated cost
      invariant cost == (sum r' | 0 <= r' < row_idx :: (sum c' | 0 <= c' < n :: (if piece_rows[r'][c'] != target_char then 1 else 0))) +
                       (sum c' | 0 <= c' < col_idx :: (if piece_rows[row_idx][c'] != target_char then 1 else 0))
    {
      if row[col_idx] != target_char then
        cost := cost + 1;
    }
  }
  cost
}

function method maximum(x: int, y: int): int { if x > y then x else y }
function method minimum(x: int, y: int): int { if x < y then x else y }

function minimum_recoloring_for_pieces(pieces: seq<seq<string>>, n: int): int
    requires |pieces| == 4
    requires n >= 1 && n % 2 == 1
    requires forall piece | piece in pieces ::
             |piece| == n &&
             (forall row | row in piece ::
                 |row| == n &&
                 (forall i | 0 <= i < |row| :: row[i] == '0' || row[i] == '1'))
    ensures 0 <= minimum_recoloring_for_pieces(pieces, n) <= 2*n*n
{
  var piece1 := pieces[0];
  var piece2 := pieces[1];
  var piece3 := pieces[2];
  var piece4 := pieces[3];

  var cost10 := calculate_recoloring_cost(piece1, n, '0');
  var cost11 := calculate_recoloring_cost(piece1, n, '1');
  var cost20 := calculate_recoloring_cost(piece2, n, '0');
  var cost21 := calculate_recoloring_cost(piece2, n, '1');
  var cost30 := calculate_recoloring_cost(piece3, n, '0');
  var cost31 := calculate_recoloring_cost(piece3, n, '1');
  var cost40 := calculate_recoloring_cost(piece4, n, '0');
  var cost41 := calculate_recoloring_cost(piece4, n, '1');

  var min_cost := 2*n*n + 1; // Initialize with a value larger than any possible cost

  // This problem describes finding the minimum recoloring cost for a 2x2 arrangement of n x n binary matrices.
  // The goal is to make each of the four n x n sub-matrices monochromatic.
  // There are two types of patterns:
  // 1. Diagonal pattern: (P1, P4) are one color, (P2, P3) are the other.
  //    (P1, P4) = '0', (P2, P3) = '1'  OR (P1, P4) = '1', (P2, P3) = '0'
  // 2. Anti-diagonal pattern: (P1, P2) are one color, (P3, P4) are the other.
  //    (P1, P2) = '0', (P3, P4) = '1'  OR (P1, P2) = '1', (P3, P4) = '0'

  // Pattern 1: (P1='0', P4='0') AND (P2='1', P3='1')
  min_cost := minimum(min_cost, cost10 + cost21 + cost31 + cost40);
  // Pattern 1: (P1='1', P4='1') AND (P2='0', P3='0')
  min_cost := minimum(min_cost, cost11 + cost20 + cost30 + cost41);

  // Pattern 2: (P1='0', P2='0') AND (P3='1', P4='1')
  min_cost := minimum(min_cost, cost10 + cost20 + cost31 + cost41);
  // Pattern 2: (P1='1', P2='1') AND (P3='0', P4='0')
  min_cost := minimum(min_cost, cost11 + cost21 + cost30 + cost40);

  min_cost
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires contains_valid_input_format(stdin_input)
    ensures is_valid_integer_string(result)
    ensures result != ""
    ensures represents_minimum_recoloring_count(stdin_input, result)
    ensures var n := extract_n_from_input(stdin_input);
            string_to_int(result) >= 0 && string_to_int(result) <= 2*n*n
// </vc-spec>
// <vc-code>
{
  var n := extract_n_from_input(stdin_input);
  var pieces := extract_pieces_from_input(stdin_input);
  var min_recolor_count := minimum_recoloring_for_pieces(pieces, n);
  result := min_recolor_count as string;
}
// </vc-code>

