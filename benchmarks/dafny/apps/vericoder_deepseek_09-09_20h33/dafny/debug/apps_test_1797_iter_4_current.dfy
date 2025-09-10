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
lemma cycle_length_positive(n: int, p: seq<int>, visited: seq<bool>, start: int)
  requires n > 0
  requires |p| == n
  requires |visited| == n
  requires 0 <= start < n
  requires forall i :: 0 <= i < n ==> 1 <= p[i] <= n
  requires forall i, j :: 0 <= i < j < n ==> p[i] != p[j]
  ensures get_cycle_length(p, visited, start) > 0
  decreases n - count_true(visited), n
{
  if !visited[start] {
    var new_visited := visited[start := true];
    cycle_length_positive(n, p, new_visited, p[start] - 1);
  }
}

lemma get_cycle_length_decreases(n: int, p: seq<int>, visited: seq<bool>, start: int, step: int) 
  requires n > 0
  requires |p| == n
  requires |visited| == n
  requires 0 <= start < n
  requires 0 <= step < n
  requires forall i :: 0 <= i < n ==> 1 <= p[i] <= n
  requires forall i, j :: 0 <= i < j < n ==> p[i] != p[j]
  ensures get_cycle_length(p, visited, start) == 1 + get_cycle_length(p, visited, p[start] - 1)
{
}

lemma mark_cycle_visited_increases_count(n: int, p: seq<int>, visited: seq<bool>, start: int)
  requires n > 0
  requires |p| == n
  requires |visited| == n
  requires 0 <= start < n
  requires forall i :: 0 <= i < n ==> 1 <= p[i] <= n
  requires forall i, j :: 0 <= i < j < n ==> p[i] != p[j]
  ensures count_true(mark_cycle_visited(p, visited, start)) > count_true(visited)
  decreases n - count_true(visited), n
{
  if !visited[start] {
    var new_visited := visited[start := true];
    mark_cycle_visited_increases_count(n, p, new_visited, p[start] - 1);
  }
}

function find_unvisited(visited: seq<bool>): int
  requires |visited| >= 0
  ensures -1 <= find_unvisited(visited) < (if |visited| > 0 then |visited| else 0)
  ensures find_unvisited(visited) >= 0 ==> !visited[find_unvisited(visited)]
  ensures find_unvisited(visited) == -1 ==> forall i :: 0 <= i < |visited| ==> visited[i]
  decreases |visited|
{
  if |visited| == 0 then -1
  else if !visited[0] then 0
  else var next := find_unvisited(visited[1..]);
       if next == -1 then -1 else next + 1
}

function get_cycle_length(p: seq<int>, visited: seq<bool>, start: int): int
  requires |p| == |visited|
  requires 0 <= start < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j]
  ensures get_cycle_length(p, visited, start) > 0
  decreases |p| - count_true(visited), |p|
{
  if visited[start] then 1 else
    var new_visited := visited[start := true];
    1 + get_cycle_length(p, new_visited, p[start] - 1)
}

function mark_cycle_visited(p: seq<int>, visited: seq<bool>, start: int): seq<bool>
  requires |p| == |visited|
  requires 0 <= start < |p|
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j]
  ensures |mark_cycle_visited(p, visited, start)| == |visited|
  ensures count_true(mark_cycle_visited(p, visited, start)) > count_true(visited)
  decreases |p| - count_true(visited), |p|
{
  if visited[start] then visited else
    var new_visited := visited[start := true];
    mark_cycle_visited(p, new_visited, p[start] - 1)
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
  result := sum_of_squares(cycle_lengths);
}
// </vc-code>

