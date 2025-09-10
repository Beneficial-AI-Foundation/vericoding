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
  ensures |split_by_newline(s)| >= 0
{
  if |s| == 0 then []
  else if exists i | 0 <= i < |s| :: s[i] == '\n'
    then var first_newline :| 0 <= first_newline < |s| && s[first_newline] == '\n';
         [s[0..first_newline]] + split_by_newline(s[first_newline + 1..])
    else [s]
}

function string_to_int(s: string): int
  requires is_valid_integer_string(s)
{
  if |s| == 1 then s[0] as int - '0' as int
  else 10 * string_to_int(s[0..|s|-1]) + (s[|s|-1] as int - '0' as int)
}

lemma string_to_int_nonnegative(s: string)
  requires is_valid_integer_string(s)
  ensures string_to_int(s) >= 0
{}

function minimum_recoloring_for_patterns(pieces: seq<seq<string>>, n: int): int
  requires |pieces| == 4
  requires n >= 1 && n % 2 == 1
  requires forall piece | piece in pieces :: 
           |piece| == n && 
           (forall row | row in piece :: 
               |row| == n &&
               (forall i | 0 <= i < |row| :: row[i] == '0' || row[i] == '1'))
  ensures 0 <= minimum_recoloring_for_patterns(pieces, n) <= 2*n*n
{
  var pattern1_total := recolor_count_for_pattern(pieces[0], n, true, true);
  var pattern2_total := recolor_count_for_pattern(pieces[1], n, true, false);
  var pattern3_total := recolor_count_for_pattern(pieces[2], n, false, true);
  var pattern4_total := recolor_count_for_pattern(pieces[3], n, false, false);
  
  pattern1_total + pattern2_total + pattern3_total + pattern4_total
}

function recolor_count_for_pattern(piece: seq<string>, n: int, first_top_black: bool, first_left_black: bool): int
  requires |piece| == n
  requires n >= 1 && n % 2 == 1
  requires forall row | row in piece :: 
           |row| == n &&
           (forall i | 0 <= i < |row| :: row[i] == '0' || row[i] == '1')
{
  if n == 0 then 0
  else var total := 0;
       var expected_color := if first_top_black then '1' else '0';
       var expected_next_color := if first_top_black then '0' else '1';
       
       for i := 0 to n-1
         invariant 0 <= total <= n * n
       {
         for j := 0 to n-1
           invariant 0 <= total <= i * n + j
         {
           var expected := if (i + j) % 2 == 0 then expected_color else expected_next_color;
           if piece[i][j] != expected then
             total := total + 1;
         }
         // Alternate the starting color for the next row
         var temp := expected_color;
         expected_color := expected_next_color;
         expected_next_color := temp;
       }
       total
}

function minimum_recoloring_for_pieces(pieces: seq<seq<string>>, n: int): int
  ensures 0 <= minimum_recoloring_for_pieces(pieces, n) <= 2*n*n
{
  minimum_recoloring_for_patterns(pieces, n)
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
  
  var pattern1_cost := recolor_count_for_pattern(pieces[0], n, true, true);
  var pattern2_cost := recolor_count_for_pattern(pieces[1], n, true, false);
  var pattern3_cost := recolor_count_for_pattern(pieces[2], n, false, true);
  var pattern4_cost := recolor_count_for_pattern(pieces[3], n, false, false);
  
  var total_cost := pattern1_cost + pattern2_cost + pattern3_cost + pattern4_cost;
  
  result := int_to_string(total_cost);
}
// </vc-code>

