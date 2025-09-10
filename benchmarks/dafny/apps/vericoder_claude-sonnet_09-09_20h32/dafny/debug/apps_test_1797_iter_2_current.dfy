predicate ValidInput(n: int, p: seq<int>)
{
  n > 0 && |p| == n &&
  (forall i :: 0 <= i < n ==> 1 <= p[i] <= n) &&
  (forall i, j :: 0 <= i < j < n ==> p[i] != p[j])
}

function count_true(visited: seq<bool>): int
  ensures count_true(visited) >= 0
  ensures count_true(visited) <= |visited|
{
  if |visited| == 0 then 0
  else (if visited[0] then 1 else 0) + count_true(visited[1..])
}

function sum_of_squares(s: seq<int>): int 
{
  if |s| == 0 then 0 else s[0] * s[0] + sum_of_squares(s[1..])
}

function get_cycle_lengths(n: int, p: seq<int>): seq<int>
  requires ValidInput(n, p)
{
  get_cycles_helper(n, p, seq(n, i => false), [])
}

function get_cycles_helper(n: int, p: seq<int>, visited: seq<bool>, cycles: seq<int>): seq<int>
  requires n > 0
  requires |p| == n
  requires |visited| == n
  requires forall i :: 0 <= i < n ==> 1 <= p[i] <= n
  requires forall i, j :: 0 <= i < j < n ==> p[i] != p[j]
  decreases n - count_true(visited)
{
  if count_true(visited) >= n then cycles
  else
    var unvisited := find_unvisited(visited);
    if unvisited == -1 then cycles
    else if 0 <= unvisited < n then
      var cycle_length := get_cycle_length(p, visited, unvisited);
      var new_visited := mark_cycle_visited(p, visited, unvisited);
      if count_true(new_visited) > count_true(visited) && count_true(new_visited) <= n then
        get_cycles_helper(n, p, new_visited, cycles + [cycle_length])
      else
        cycles + [cycle_length]
    else
      cycles
}

// <vc-helpers>
function find_unvisited(visited: seq<bool>): int
  ensures find_unvisited(visited) == -1 ==> forall i :: 0 <= i < |visited| ==> visited[i]
  ensures find_unvisited(visited) != -1 ==> 0 <= find_unvisited(visited) < |visited| && !visited[find_unvisited(visited)]
{
  find_unvisited_helper(visited, 0)
}

function find_unvisited_helper(visited: seq<bool>, index: int): int
  requires 0 <= index <= |visited|
  ensures find_unvisited_helper(visited, index) == -1 ==> forall i :: index <= i < |visited| ==> visited[i]
  ensures find_unvisited_helper(visited, index) != -1 ==> index <= find_unvisited_helper(visited, index) < |visited| && !visited[find_unvisited_helper(visited, index)]
{
  if index >= |visited| then -1
  else if !visited[index] then index
  else find_unvisited_helper(visited, index + 1)
}

function get_cycle_length(p: seq<int>, visited: seq<bool>, start: int): int
  requires |p| == |visited|
  requires 0 <= start < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  ensures get_cycle_length(p, visited, start) > 0
{
  get_cycle_length_helper(p, start, start, 1)
}

function get_cycle_length_helper(p: seq<int>, start: int, current: int, length: int): int
  requires |p| > 0
  requires 0 <= start < |p|
  requires 0 <= current < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires length > 0
  ensures get_cycle_length_helper(p, start, current, length) > 0
{
  var next := p[current] - 1;
  if 0 <= next < |p| && next == start then length
  else if 0 <= next < |p| then get_cycle_length_helper(p, start, next, length + 1)
  else length
}

function mark_cycle_visited(p: seq<int>, visited: seq<bool>, start: int): seq<bool>
  requires |p| == |visited|
  requires 0 <= start < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  ensures |mark_cycle_visited(p, visited, start)| == |visited|
{
  mark_cycle_visited_helper(p, visited, start, start)
}

function mark_cycle_visited_helper(p: seq<int>, visited: seq<bool>, start: int, current: int): seq<bool>
  requires |p| == |visited|
  requires 0 <= start < |p|
  requires 0 <= current < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  ensures |mark_cycle_visited_helper(p, visited, start, current)| == |visited|
{
  var new_visited := visited[current := true];
  var next := p[current] - 1;
  if 0 <= next < |p| && next == start then new_visited
  else if 0 <= next < |p| && !new_visited[next] then mark_cycle_visited_helper(p, new_visited, start, next)
  else new_visited
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: seq<int>) returns (result: int)
  requires ValidInput(n, p)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  var cycle_lengths := get_cycle_lengths(n, p);
  if |cycle_lengths| == 0 then
    result := 1;
  else
    result := sum_of_squares(cycle_lengths);
    if result <= 0 then
      result := 1;
}
// </vc-code>

