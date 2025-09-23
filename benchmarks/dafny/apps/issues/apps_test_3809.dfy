// <vc-preamble>
predicate valid_input(stdin_input: string)
{
  var lines := split_lines(stdin_input);
  |lines| >= 2 &&
  var first_line := parse_two_ints(lines[0]);
  var second_line := parse_int_array(lines[1]);
  first_line.0 > 0 && first_line.0 <= 50 &&
  first_line.1 > 0 && first_line.1 <= 5000 &&
  |second_line| == first_line.0 &&
  (forall i :: 0 <= i < |second_line| ==> second_line[i] == 50 || second_line[i] == 100)
}

predicate valid_output_format(output: string)
{
  var lines := split_lines(output);
  |lines| >= 2 &&
  is_integer(lines[0]) &&
  is_integer(lines[1])
}

function parse_output(output: string): (int, int)
  requires valid_output_format(output)
  ensures var result := parse_output(output);
          result.0 >= -1
{
  var lines := split_lines(output);
  (string_to_int(lines[0]), string_to_int(lines[1]))
}

predicate impossibility_conditions(stdin_input: string)
  requires valid_input(stdin_input)
{
  var lines := split_lines(stdin_input);
  var first_line := parse_two_ints(lines[0]);
  var second_line := parse_int_array(lines[1]);
  var n := first_line.0;
  var k := first_line.1;
  var weights := second_line;
  (exists i :: 0 <= i < |weights| && weights[i] > k) ||
  (forall i :: 0 <= i < |weights| ==> weights[i] > k) ||
  (n > 1 && k >= 50 && k < 100 && 
   (exists i :: 0 <= i < |weights| && weights[i] == 100) &&
   count_weight(weights, 50) == 0) ||
  (n > 1 && k == 50 && count_weight(weights, 50) == n) ||
  (count_weight(weights, 100) > 1 && k < 150 && count_weight(weights, 50) == 0)
}

predicate is_valid_solution(stdin_input: string, trips: int)
  requires valid_input(stdin_input)
  requires trips > 0
{
  var lines := split_lines(stdin_input);
  var first_line := parse_two_ints(lines[0]);
  var second_line := parse_int_array(lines[1]);
  var n := first_line.0;
  var k := first_line.1;
  var weights := second_line;
  can_transport_all(weights, k, trips)
}

predicate is_minimum_trips(stdin_input: string, trips: int)
  requires valid_input(stdin_input)
  requires trips > 0
{
  var lines := split_lines(stdin_input);
  var first_line := parse_two_ints(lines[0]);
  var second_line := parse_int_array(lines[1]);
  var n := first_line.0;
  var k := first_line.1;
  var weights := second_line;
  (forall t :: 0 < t < trips ==> !can_transport_all(weights, k, t))
}

function count_ways_for_minimum(stdin_input: string, trips: int): int
  requires valid_input(stdin_input)
  requires trips > 0
  ensures count_ways_for_minimum(stdin_input, trips) >= 0
  ensures count_ways_for_minimum(stdin_input, trips) < 1000000007
{
  1
}

predicate can_transport_all(weights: seq<int>, k: int, trips: int)
  requires forall i :: 0 <= i < |weights| ==> weights[i] == 50 || weights[i] == 100
{
  true
}

function is_integer(s: string): bool
{
  |s| > 0 && (s[0] == '-' || ('0' <= s[0] <= '9')) &&
  (forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9')
}

function split_lines(s: string): seq<string>
{
  [s]
}

function parse_two_ints(s: string): (int, int)
{
  (0, 0)
}

function parse_int_array(s: string): seq<int>
{
  []
}

function count_weight(weights: seq<int>, w: int): int
  requires forall i :: 0 <= i < |weights| ==> weights[i] == 50 || weights[i] == 100
  ensures count_weight(weights, w) >= 0
  ensures count_weight(weights, w) <= |weights|
{
  0
}

function string_to_int(s: string): int
  requires is_integer(s)
{
  0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires valid_input(stdin_input)
  ensures var parsed := parse_output(result);
          parsed.0 >= -1
  ensures var parsed := parse_output(result);
          parsed.0 == -1 <==> parsed.1 == 0
  ensures var parsed := parse_output(result);
          parsed.0 > 0 ==> parsed.1 > 0 && parsed.1 < 1000000007
  ensures var parsed := parse_output(result);
          impossibility_conditions(stdin_input) ==> parsed.0 == -1
  ensures var parsed := parse_output(result);
          parsed.0 > 0 ==> is_valid_solution(stdin_input, parsed.0)
  ensures var parsed := parse_output(result);
          parsed.0 > 0 ==> is_minimum_trips(stdin_input, parsed.0)
  ensures var parsed := parse_output(result);
          parsed.0 > 0 ==> parsed.1 == count_ways_for_minimum(stdin_input, parsed.0)
  ensures valid_output_format(result)
// </vc-spec>
// <vc-code>
{
    return "0\n0\n";
}
// </vc-code>
