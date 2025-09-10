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
function find_unvisited_help(visited: seq<bool>, start: int): (r: int)
  decreases |visited| - start
{
  if start >= |visited| then -1
  else if !visited[start] then start
  else find_unvisited_help(visited, start + 1)
}

function find_unvisited(visited: seq<bool>): (r: int)
{
  find_unvisited_help(visited, 0)
}

function get_cycle_length_help(p: seq<int>, current: int, start: int, count: int): int
  decreases |p| - count
  requires 0 <= current < |p|
{
  if current == start then count
  else get_cycle_length_help(p, p[current] - 1, start, count + 1)
}

function get_cycle_length(p: seq<int>, visited: seq<bool>, start: int): int
  requires |p| == |visited|
  requires 0 <= start < |visited|
{
  get_cycle_length_help(p, p[start] - 1, start, 1)
}

function mark_cycle_visited_help(p: seq<int>, visited: seq<bool>, current: int, start: int): seq<bool>
  requires 0 <= current < |visited|
{
  if current == start then visited
  else
    var temp := visited[current := true];
    mark_cycle_visited_help(p, temp, p[current] - 1, start)
}

function mark_cycle_visited(p: seq<int>, visited: seq<bool>, start: int): seq<bool>
  requires |p| == |visited|
  requires 0 <= start < |visited|
{
  var temp := visited[start := true];
  if p[start] - 1 == start then temp
  else mark_cycle_visited_help(p, temp, p[start] - 1, start)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: seq<int>) returns (result: int)
  requires ValidInput(n, p)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  result := sum_of_squares(get_cycle_lengths(n, p));
}
// </vc-code>

