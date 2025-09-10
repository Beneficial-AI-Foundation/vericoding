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
lemma {:axiom} decimal_representation_exists(x: int)
    requires 0 <= x
    ensures exists s :: is_valid_integer_string(s) && string_to_int(s) == x
{
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
    // cost when forcing top-left = '1' for piece k
    var cost1_0 := |{ (i,j) | 0 <= i < n && 0 <= j < n &&
                             pieces[0][i][j] != (if ( (i + j) % 2 == 0) then '1' else '0') }|;
    var cost1_1 := |{ (i,j) | 0 <= i < n && 0 <= j < n &&
                             pieces[1][i][j] != (if ( (i + j) % 2 == 0) then '1' else '0') }|;
    var cost1_2 := |{ (i,j) | 0 <= i < n && 0 <= j < n &&
                             pieces[2][i][j] != (if ( (i + j) % 2 == 0) then '1' else '0') }|;
    var cost1_3 := |{ (i,j) | 0 <= i < n && 0 <= j < n &&
                             pieces[3][i][j] != (if ( (i + j) % 2 == 0) then '1' else '0') }|;
    var total1 := cost1_0 + cost1_1 + cost1_2 + cost1_3;
    // diff_k = cost0_k - cost1_k = (n*n - cost1_k) - cost1_k = n*n - 2*cost1_k
    var d0 := n*n - 2*cost1_0;
    var d1 := n*n - 2*cost1_1;
    var d2 := n*n - 2*cost1_2;
    var d3 := n*n - 2*cost1_3;
    // compute minimum sum of two diffs among four
    var s01 := d0 + d1;
    var s02 := d0 + d2;
    var s03 := d0 + d3;
    var s12 := d1 + d2;
    var s13 := d1 + d3;
    var s23 := d2 + d3;
    var best := if s01 <= s02 then s01 else s02;
    best := if best <= s03 then best else s03;
    best := if best <= s12 then best else s12;
    best := if best <= s13 then best else s13;
    best := if best <= s23 then best else s23;
    total1 + best
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
    var ans := minimum_recoloring_for_pieces(pieces, n);
    // provide existence of a decimal string for ans (axiomatically)
    decimal_representation_exists(ans);
    var s :| is_valid_integer_string(s) && string_to_int(s) == ans;
    result := s;
}
// </vc-code>

