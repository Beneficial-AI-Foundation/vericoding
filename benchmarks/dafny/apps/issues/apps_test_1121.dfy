// <vc-preamble>
function concat_lines(lines: seq<string>): string
  requires |lines| > 0
  ensures |concat_lines(lines)| > 0
  ensures concat_lines(lines)[|concat_lines(lines)|-1] == '\n'
{
  if |lines| == 1 then lines[0] + "\n"
  else lines[0] + "\n" + concat_lines(lines[1..])
}

predicate valid_square_coloring(lines: seq<string>, n: nat, m: nat)
  requires |lines| == n
  requires forall i :: 0 <= i < n ==> |lines[i]| == m
{
  forall i, j :: 0 <= i < n && 0 <= j < m ==>
    exists size, top_i, left_j :: 1 <= size <= n && size <= m &&
      top_i <= i < top_i + size &&
      left_j <= j < left_j + size &&
      top_i + size <= n && left_j + size <= m &&
      (forall k, l :: top_i <= k < top_i + size && left_j <= l < left_j + size &&
                      0 <= k < n && 0 <= l < m ==>
        lines[k][l] == lines[i][j]) &&
      (forall k, l :: 
        ((k == top_i - 1 && left_j <= l < left_j + size) ||
         (k == top_i + size && left_j <= l < left_j + size) ||
         (top_i <= k < top_i + size && l == left_j - 1) ||
         (top_i <= k < top_i + size && l == left_j + size)) &&
         0 <= k < n && 0 <= l < m ==>
        lines[k][l] != lines[i][j])
}

predicate lexicographically_smaller_or_equal(lines1: seq<string>, lines2: seq<string>, n: nat, m: nat)
  requires |lines1| == n && |lines2| == n
  requires forall i :: 0 <= i < n ==> |lines1[i]| == m && |lines2[i]| == m
{
  exists i, j :: 0 <= i < n && 0 <= j < m &&
    (forall k, l :: (k < i || (k == i && l < j)) && 0 <= k < n && 0 <= l < m ==>
     lines1[k][l] == lines2[k][l]) &&
    (lines1[i][j] < lines2[i][j] || 
     (lines1[i][j] == lines2[i][j] && 
      forall k, l :: 0 <= k < n && 0 <= l < m ==> lines1[k][l] == lines2[k][l]))
}

predicate squares_are_maximal_at_creation(lines: seq<string>, n: nat, m: nat)
  requires |lines| == n
  requires forall i :: 0 <= i < n ==> |lines[i]| == m
{
  forall i, j :: 0 <= i < n && 0 <= j < m ==>
    (is_top_left_of_square(i, j, lines, n, m) ==>
     largest_possible_square_at_position(i, j, lines, n, m))
}

predicate is_top_left_of_square(i: nat, j: nat, lines: seq<string>, n: nat, m: nat)
  requires |lines| == n
  requires forall k :: 0 <= k < n ==> |lines[k]| == m
  requires i < n && j < m
{
  exists size :: size >= 1 && i + size <= n && j + size <= m &&
    (forall k, l :: i <= k < i + size && j <= l < j + size ==>
     lines[k][l] == lines[i][j]) &&
    (i == 0 || lines[i-1][j] != lines[i][j]) &&
    (j == 0 || lines[i][j-1] != lines[i][j])
}

predicate largest_possible_square_at_position(i: nat, j: nat, lines: seq<string>, n: nat, m: nat)
  requires |lines| == n
  requires forall k :: 0 <= k < n ==> |lines[k]| == m
  requires i < n && j < m
{
  var max_size := if n - i <= m - j then n - i else m - j;
  exists size :: 1 <= size <= max_size && 
    square_at_position(i, j, size, lines, n, m) &&
    !can_extend_square_at_position(i, j, size + 1, lines[i][j], lines, n, m)
}

predicate square_at_position(i: nat, j: nat, size: nat, lines: seq<string>, n: nat, m: nat)
  requires |lines| == n
  requires forall k :: 0 <= k < n ==> |lines[k]| == m
  requires i < n && j < m
{
  i + size <= n && j + size <= m &&
  (forall k, l :: i <= k < i + size && j <= l < j + size ==>
   lines[k][l] == lines[i][j])
}

predicate can_extend_square_at_position(i: nat, j: nat, size: nat, color: char, 
                                       lines: seq<string>, n: nat, m: nat)
  requires |lines| == n
  requires forall k :: 0 <= k < n ==> |lines[k]| == m
  requires i < n && j < m
{
  i + size <= n && j + size <= m &&
  (forall k, l :: 
    ((k == i - 1 && j <= l < j + size) ||
     (k == i + size && j <= l < j + size) ||
     (i <= k < i + size && l == j - 1) ||
     (i <= k < i + size && l == j + size)) &&
     0 <= k < n && 0 <= l < m ==>
    lines[k][l] != color)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == ' '
  requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
  requires exists n, m, space_pos, newline_pos :: 
    n >= 1 && m >= 1 && n <= 100 && m <= 100 &&
    0 < space_pos < newline_pos < |stdin_input| &&
    stdin_input[space_pos] == ' ' &&
    stdin_input[newline_pos] == '\n' &&
    (forall k :: 0 <= k < space_pos ==> stdin_input[k] in "0123456789") &&
    (forall k :: space_pos < k < newline_pos ==> stdin_input[k] in "0123456789")
  ensures |result| > 0
  ensures result[|result|-1] == '\n'
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] in
// </vc-spec>
// <vc-code>
{'A', 'B', 'C', 'D', 'E', 'F', '\n'}
// </vc-code>
