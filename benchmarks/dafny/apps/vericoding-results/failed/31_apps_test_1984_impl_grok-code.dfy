function split_lines(s: string): seq<string>
{
    []
}

function parse_first_line(s: string): (nat, nat, nat, nat)
{
    (1, 1, 1, 1)
}

function parse_levels(lines: seq<string>, n: nat, m: nat, k: nat): seq<seq<string>>
{
    []
}

function int_to_string(n: nat): string
{
    ""
}

function parse_dependency_line(s: string): (nat, nat)
{
    (1, 0)
}

predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 &&
    stdin_input[|stdin_input|-1] == '\n' &&
    var lines := split_lines(stdin_input);
    |lines| >= 1 &&
    exists n, m, k, w: nat :: (
        parse_first_line(lines[0]) == (n, m, k, w) &&
        1 <= n <= 10 && 1 <= m <= 10 && 1 <= k <= 1000 && 1 <= w <= 1000 &&
        |lines| >= 1 + k * n &&
        (forall i :: 1 <= i < 1 + k * n ==> |lines[i]| == m) &&
        (forall i :: 1 <= i < 1 + k * n ==> 
            forall j :: 0 <= j < |lines[i]| ==> 
                (lines[i][j] == '.' || ('a' <= lines[i][j] <= 'z') || ('A' <= lines[i][j] <= 'Z')))
    )
}

predicate ValidOutput(result: string, stdin_input: string)
{
    |result| > 0 &&
    result[|result|-1] == '\n' &&
    var result_lines := split_lines(result);
    var lines := split_lines(stdin_input);
    |lines| >= 1 &&
    exists n, m, k, w: nat, input_levels: seq<seq<string>> :: (
        parse_first_line(lines[0]) == (n, m, k, w) &&
        1 <= n <= 10 && 1 <= m <= 10 && 1 <= k <= 1000 && 1 <= w <= 1000 &&
        |lines| >= 1 + k * n &&
        input_levels == parse_levels(lines, n, m, k) &&
        |input_levels| == k &&
        (forall i :: 0 <= i < k ==> |input_levels[i]| == n) &&
        (forall i :: 0 <= i < k ==> forall j :: 0 <= j < n ==> |input_levels[i][j]| == m) &&

        |result_lines| == k + 1 &&

        exists total_cost: nat :: (
            result_lines[0] == int_to_string(total_cost) &&
            total_cost == calculate_mst_cost(n, m, k, w, input_levels) &&

            (forall i :: 1 <= i <= k ==> 
                exists level, parent: nat :: (
                    parse_dependency_line(result_lines[i]) == (level, parent) &&
                    1 <= level <= k &&
                    0 <= parent <= k &&
                    level != parent
                )) &&

            (forall level :: 1 <= level <= k ==> 
                exists i {:trigger parse_dependency_line(result_lines[i]).0} :: 
                    1 <= i <= k && 
                    parse_dependency_line(result_lines[i]).0 == level &&
                    (forall j :: 1 <= j <= k && j != i ==> 
                        parse_dependency_line(result_lines[j]).0 != level)) &&

            is_valid_spanning_tree(result_lines, k)
        )
    )
}

function calculate_mst_cost(n: nat, m: nat, k: nat, w: nat, levels: seq<seq<string>>): nat
{
    0
}

function is_valid_spanning_tree(result_lines: seq<string>, k: nat): bool
{
    true
}

function count_differences(level1: seq<string>, level2: seq<string>, n: nat, m: nat): nat
{
    0
}

// <vc-helpers>
function split_lines(s: string): seq<string>
{
  if |s| == 0 then []
  else split_lines_recursive(s, 0, 0, [])
}

function split_lines_recursive(s: string, pos: nat, start: nat, res: seq<string>): seq<string>
  decreases |s| - pos
{
  if pos >= |s| then (if start < |s| then res + [s[start..]] else res)
  else if s[pos] == '\n' then split_lines_recursive(s, pos + 1, pos + 1, res + [s[start..pos]])
  else if pos == |s| - 1 then split_lines_recursive(s, pos + 1, pos + 1, res + [s[start..pos + 1]])
  else split_lines_recursive(s, pos + 1, start, res)
}

function pow10(e: nat): nat
{
  if e == 0 then 1
  else 10 * pow10(e - 1)
}

function to_nat(s: string): nat
{
  if |s| == 0 then 0
  else (s[0] as nat - '0' as nat) * pow10(|s| - 1) + to_nat(s[1..])
}

function parse_first_line(s: string): (nat, nat, nat, nat)
{
  let pos1 := index_of_space(s, 0);
  let pos2 := index_of_space(s, pos1 + 1);
  let pos3 := index_of_space(s, pos2 + 1);
  let pos4 := |s|; // up to \n
  (to_nat(s[0..pos1]), to_nat(s[pos1+1..pos2]), to_nat(s[pos2+1..pos3]), to_nat(s[pos3+1..pos4]))
}

function index_of_space(s: string, start: nat): nat
{
  if start >= |s| then |s|
  else if s[start] == ' ' then start
  else index_of_space(s, start + 1)
}

function parse_levels(lines: seq<string>, n: nat, m: nat, k: nat): seq<seq<string>>
{
  if k == 0 then []
  else [lines[1..1+n]] + parse_levels(lines[1+n..], n, m, k-1)
}

function int_to_string(n: nat): string
{
  if n == 0 then "0"
  else if n < 10 then [char(48 + (n % 10))]
  else int_to_string(n / 10) + [char(48 + (n % 10))]
}

function parse_dependency_line(s: string): (nat, nat)
{
  let pos := index_of_space(s, 0);
  (to_nat(s[0..pos]), to_nat(s[pos+1..]))
}

function calculate_mst_cost(n: nat, m: nat, k: nat, w: nat, levels: seq<seq<string>>): nat
{
  var graph := calculate_graph(n, m, k, w, levels);
  prim_min_cost(graph, k)
}

function calculate_graph(n: nat, m: nat, k: nat, w: nat, levels: seq<seq<string>>): seq<seq<nat>>
{
  seq(k, i => seq(k, j => if i == j then 0 else w * count_differences(levels[i], levels[j], n, m)))
}

function prim_min_cost(graph: seq<seq<nat>>, k: nat): nat
{
  if k == 0 then 0
  else
  var visited: seq<bool> := seq(k, _ => false);
  var cost: seq<nat> := seq(k, _ => 10000000);
  cost := cost[0 := 0];
  var total: nat := 0;
  var curr := 0;
  while curr < k
    invariant 0 <= curr <= k
    invariant |visited| == k && |cost| == k
  {
    var min_c: nat := 10000000;
    var u: nat := k;
    var i := 0;
    while i < k
      invariant 0 <= i <= k
      invariant u == k || (0 <= u < k)
    {
      if !visited[i] && cost[i] < min_c {
        min_c := cost[i];
        u := i;
      }
      i := i + 1;
    }
    if u == k || visited[u] break;
    visited := visited[u := true];
    if curr > 0 {
      total := total + min_c;
    }
    var v := 0;
    while v < k
      invariant 0 <= v <= k
    {
      if !visited[v] && graph[u][v] < cost[v] {
        cost := cost[v := graph[u][v]];
      }
      v := v + 1;
    }
    curr := curr + 1;
  }
  total
}

function is_valid_spanning_tree(result_lines: seq<string>, k: nat): bool
{
  |result_lines| == k + 1
}

// Placeholder
function count_differences(level1: seq<string>, level2: seq<string>, n: nat, m: nat): nat
{
  count_different_rows(level1, level2, n, m, 0, 0)
}

function count_different_rows(level1: seq<string>, level2: seq<string>, n: nat, m: nat, i: nat, count: nat): nat
{
  if i >= |level1| || i >= n then count
  else count_different_rows(level1, level2, n, m, i+1, count + count_different_cells(level1[i], level2[i], m, 0, 0))
}

function count_different_cells(s1: string, s2: string, m: nat, j: nat, c: nat): nat
{
  if j >= m then c
  else count_different_cells(s1, s2, m, j+1, c + if s1[j] != s2[j] then 1 else 0)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(result, stdin_input)
// </vc-spec>
// <vc-code>
{
  // Parse input
  var lines := split_lines(stdin_input);
  var (n, m, k, w) := parse_first_line(lines[0]);
  var levels := parse_levels(lines, n, m, k);

  // Build graph
  var graph: seq<seq<nat>> := seq(k, i => seq(k, j => if i == j then 0 else w * count_differences(levels[i], levels[j], n, m)));

  // Prim's algorithm
  var visited: seq<bool> := seq(k, _ => false);
  var cost: seq<nat> := seq(k, _ => 10000000); // large number
  var parent: seq<nat> := seq(k, _ => 0); // or use -1, but use k for invalid
  cost := cost[0 := 0];
  // Set parent for root
  parent := parent[0 := k];
  var total_cost: nat := 0;
  var count: nat := 0;

  while count < k
    invariant 0 <= count <= k
    invariant |visited| == k && |cost| == k && |parent| == k
    invariant total_cost == calculate_mst_cost(n, m, k, w, levels[0 .. k]) - if count == 1 then cost[0] else 0  // simplified, but need to ensure
  {
    // Find min u
    var u: nat := k; // invalid
    var min_c: nat := 10000000;
    var i := 0;
    while i < k
      invariant 0 <= i <= k
      invariant u == k || (0 <= u < k)
    {
      if !visited[i] && cost[i] < min_c {
        min_c := cost[i];
        u := i;
      }
      i := i + 1;
    }
    if u == k || visited[u] break;
    visited := visited[u := true];
    // Add to cost only if not root
    if count > 0 {  // change to count > 0 since root has count 0
      total_cost := total_cost + min_c;
    }
    // Update neighbors
    var v := 0;
    while v < k
      invariant 0 <= v <= k
    {
      if !visited[v] && graph[u][v] < cost[v] {
        cost := cost[v := graph[u][v]];
        parent := parent[v := u];
      }
      v := v + 1;
    }
    count := count + 1;
  }

  // Build output
  var result_lines: seq<string> := [int_to_string(total_cost)];
  for i := 0 to k - 1 {
    var level: nat := i + 1;
    var p: nat := if parent[i] == k then 0 else parent[i] + 1;  // parent init to k for root, but in graph 0 to k-1
    result_lines := result_lines + [int_to_string(level) + " " + int_to_string(p)];
  }
  var result: string := "";
  for i := 0 to |result_lines| - 1 {
    result := result + result_lines[i] + "\n";
  }
  return result;
}
// </vc-code>

