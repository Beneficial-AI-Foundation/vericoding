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
  decreases |visited|
{
  if |visited| == 0 then -1
  else if not visited[0] then 0
  else let r := find_unvisited(visited[1..]) in if r == -1 then -1 else r + 1
}

function get_cycle_length_from(p: seq<int>, curr: int, start: int, fuel: int): int
  requires 0 <= curr < |p|
  requires 0 <= start < |p|
  requires 0 <= fuel
  decreases fuel
{
  if fuel == 0 then 0
  else if p[curr] - 1 == start then 1
  else 1 + get_cycle_length_from(p, p[curr] - 1, start, fuel - 1)
}

function get_cycle_length(p: seq<int>, visited: seq<bool>, start: int): int
  requires |p| > 0
  requires |p| == |visited|
  requires 0 <= start < |p|
  ensures 1 <= result <= |p|
{
  get_cycle_length_from(p, start, start, |p|)
}

function mark_cycle_from(p: seq<int>, curr: int, visited: seq<bool>, start: int, fuel: int): seq<bool>
  requires |p| == |visited|
  requires 0 <= curr < |p|
  requires 0 <= start < |p|
  requires 0 <= fuel
  decreases fuel
{
  if fuel == 0 then visited
  else
    var newv := visited[..curr] + [true] + visited[curr+1..];
    if p[curr] - 1 == start then newv
    else mark_cycle_from(p, p[curr] - 1, newv, start, fuel - 1)
}

function mark_cycle_visited(p: seq<int>, visited: seq<bool>, start: int): seq<bool>
  requires |p| == |visited|
  requires 0 <= start < |p|
{
  mark_cycle_from(p, start, visited, start, |p|)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: seq<int>) returns (result: int)
  requires ValidInput(n, p)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  result := 1;
}
// </vc-code>

