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
    []
  else
    var parts := new List<string>();
    var current_index := 0;
    while current_index < |s|
      invariant 0 <= current_index <= |s|
      invariant forall i | 0 <= i < |parts| :: parts[i] != "" ==> !parts[i].Contains('\n')
      decrease |s| - current_index
    {
      var newline_index := s.IndexOf('\n', current_index);
      if newline_index == -1
      {
        parts.Add(s.Substring(current_index));
        current_index := |s|;
      }
      else
      {
        parts.Add(s.Substring(current_index, newline_index - current_index));
        current_index := newline_index + 1;
      }
    }
    parts.Elements
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
    invariant n == (if i == 0 then 0 else string_to_int(s[0..i]))
    reads s
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
  {
    var row := piece_rows[row_idx];
    for col_idx := 0 to n - 1
      invariant 0 <= col_idx <= n
      invariant 0 <= cost <= row_idx * n + col_idx
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

  var min_cost := n * n * 2 + 1; // Initialize with a value larger than any possible cost

  // Case (P1,P2) = ('0','0'), (P3,P4) any
  min_cost := minimum(min_cost, cost10 + cost20 + minimum(cost30 + cost41, cost31 + cost40));

  // Case (P1,P2) = ('0','1'), (P3,P4) any
  min_cost := minimum(min_cost, cost10 + cost21 + minimum(cost30 + cost41, cost31 + cost40));

  // Case (P1,P2) = ('1','0'), (P3,P4) any
  min_cost := minimum(min_cost, cost11 + cost20 + minimum(cost30 + cost41, cost31 + cost40));

  // Case (P1,P2) = ('1','1'), (P3,P4) any
  min_cost := minimum(min_cost, cost11 + cost21 + minimum(cost30 + cost41, cost31 + cost40));

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

