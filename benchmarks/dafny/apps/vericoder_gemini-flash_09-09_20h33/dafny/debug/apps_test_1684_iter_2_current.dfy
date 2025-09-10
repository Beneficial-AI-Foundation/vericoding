datatype InputData = InputData(n: int, m: int, segments: set<(int, int)>)

predicate valid_input_format(stdin_input: string)
{
    |stdin_input| > 0
}

function parse_input(stdin_input: string): InputData
requires valid_input_format(stdin_input)
{
    InputData(2, 0, {})
}

function rotate_segment(seg: (int, int), k: int, n: int): (int, int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires k >= 0 && n > 0
{
    var a := var temp_a := (seg.0 + k) % n; if temp_a == 0 then n else temp_a;
    var b := var temp_b := (seg.1 + k) % n; if temp_b == 0 then n else temp_b;
    (a, b)
}

predicate exists_rotational_symmetry(data: InputData)
{
    exists k :: 1 <= k < data.n && 
        data.n % k == 0 &&
        (forall seg :: seg in data.segments ==> 
            seg.0 >= 1 && seg.0 <= data.n && seg.1 >= 1 && seg.1 <= data.n &&
            rotate_segment(seg, k, data.n) in data.segments)
}

// <vc-helpers>
function parse_int(s: string): int
  reads s
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  var x := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant x == (if i == 0 then 0 else (var res := 0; for k := 0 to i-1 { res := res * 10 + (s[k] - '0'); } return res;))
  {
    x := x * 10 + (s[i] - '0');
    i := i + 1;
  }
  return x;
}

function parse_n_m(s: string): (int, int)
  requires " " in s
  requires var parts := s.Split(' '); |parts| == 2
  requires forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9'
  requires forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9'
{
  var parts := s.Split(' ');
  (parse_int(parts[0]), parse_int(parts[1]))
}

function parse_segment_str(s: string): (int, int)
  requires " " in s
  requires var parts := s.Split(' '); |parts| == 2
  requires forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9'
  requires forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9'
{
  var parts := s.Split(' ');
  (parse_int(parts[0]), parse_int(parts[1]))
}

function parse_input_full(stdin_input: string): InputData
requires valid_input_format(stdin_input)
{
  var lines := stdin_input.Split('\n');
  var n_m_line := lines[0];
  var n, m := parse_n_m(n_m_line);

  var segments_set := set of (int, int);
  var i := 1;
  while i < |lines|
    invariant 1 <= i <= |lines|
    invariant forall j :: 1 <= j < i ==> var seg_parts := lines[j].Split(' '); |seg_parts| == 2 && forall k :: 0 <= k < |seg_parts[0]| ==> '0' <= seg_parts[0][k] <= '9' && forall k :: 0 <= k < |seg_parts[1]| ==> '0' <= seg_parts[1][k] <= '9'
    invariant segments_set == set x | (exists index :: 1 <= index < i && parse_segment_str(lines[index]) == x)
  {
    var segment_line := (lines[i]);
    if |segment_line| > 0 { // Check for empty lines, especially the last one
      segments_set := segments_set + {parse_segment_str(segment_line)};
    }
    i := i + 1;
  }
  InputData(n, m, segments_set)
}

predicate valid_input_format(stdin_input: string)
{
  |stdin_input| > 0 &&
  var lines := stdin_input.Split('\n');
  |lines| >= 1 &&
  var n_m_line := lines[0];
  " " in n_m_line &&
  var n_m_parts := n_m_line.Split(' ');
  |n_m_parts| == 2 &&
  (forall c :: c in n_m_parts[0] ==> '0' <= c <= '9') &&
  (forall c :: c in n_m_parts[1] ==> '0' <= c <= '9') &&
  var n_val := parse_int(n_m_parts[0]);
  var m_val := parse_int(n_m_parts[1]);
  n_val > 0 && m_val >= 0 &&
  (|lines| == m_val + 1 || (|lines| == m_val + 2 && lines[m_val+1] == "")) && // Allow for a trailing empty line
  (forall i :: 1 <= i < |lines| ==>
    var seg_line := lines[i];
    (|seg_line| == 0 || (" " in seg_line &&
    var seg_parts := seg_line.Split(' ');
    |seg_parts| == 2 &&
    (forall c :: c in seg_parts[0] ==> '0' <= c <= '9') &&
    (forall c :: c in seg_parts[1] ==> '0' <= c <= '9'))))
}

function rotate_segment(seg: (int, int), k: int, n: int): (int, int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires k >= 0 && n > 0
{
    var a := ((seg.0 - 1 + k) % n) + 1; // Adjust to 0-indexed for modulo, then back to 1-indexed
    var b := ((seg.1 - 1 + k) % n) + 1; // Adjust to 0-indexed for modulo, then back to 1-indexed
    (a, b)
}

predicate exists_rotational_symmetry(data: InputData)
{
    exists k :: 1 <= k < data.n && 
        data.n % k == 0 &&
        (forall seg :: seg in data.segments ==> 
            seg.0 >= 1 && seg.0 <= data.n && seg.1 >= 1 && seg.1 <= data.n &&
            rotate_segment(seg, k, data.n) in data.segments)
}

function parse_input(stdin_input: string): InputData
requires valid_input_format(stdin_input)
{
    parse_input_full(stdin_input)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
requires valid_input_format(stdin_input)
ensures result == "Yes" || result == "No"
ensures result == "Yes" <==> exists_rotational_symmetry(parse_input(stdin_input))
// </vc-spec>
// <vc-code>
{
  var data := parse_input(stdin_input);
  if exists_rotational_symmetry(data) then
    result := "Yes"
  else
    result := "No";
  return result;
}
// </vc-code>

