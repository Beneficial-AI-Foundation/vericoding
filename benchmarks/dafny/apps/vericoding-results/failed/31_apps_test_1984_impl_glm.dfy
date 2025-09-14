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
    if s == "" then [] else
    var index := 0;
    var lines := [];
    var start := 0;
    while index < |s|
        invariant 0 <= start <= index <= |s|
        invariant forall i :: 0 <= i < |lines| ==> lines[i] == s[start..index] at i
    {
        if s[index] == '\n' then
            lines := lines + [s[start..index]];
            start := index + 1;
        index := index + 1;
    }
    lines
}

function parse_first_line(s: string): (n: nat, m: nat, k: nat, w: nat)
    requires s != "" && s[|s|-1] == '\n'
{
    var s_clean := s[..|s|-1];
    var parts := split_at_spaces(s_clean);
    (parse_nat(parts[0]), parse_nat(parts[1]), parse_nat(parts[2]), parse_nat(parts[3]))
}

function split_at_spaces(s: string): seq<string>
{
    if |s| == 0 then [] else
    var index := 0;
    var parts := [];
    var start := 0;
    while index < |s|
        invariant 0 <= start <= index <= |s|
        invariant forall i :: 0 <= i < |parts| ==> parts[i] == s[start..index] at i
    {
        if s[index] == ' ' then
            parts := parts + [s[start..index]];
            start := index + 1;
        index := index + 1;
    }
    if start < |s| then parts := parts + [s[start..index]];
    parts
}

function parse_nat(s: string): nat
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures parse_nat(s) < 1000000 // reasonable bound
{
    if |s| == 0 then 0 else
        parse_nat(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int) as nat
}

function parse_levels(lines: seq<string>, n: nat, m: nat, k: nat): seq<seq<string>>
    requires |lines| >= 1 + k * n
    requires forall i :: 1 <= i < 1 + k * n ==> |lines[i]| == m
{
    var levels := [];
    var level_idx := 0;
    while level_idx < k
        invariant 0 <= level_idx <= k
        invariant |levels| == level_idx
        invariant forall i :: 0 <= i < level_idx ==> |levels[i]| == n
    {
        var curr_level := [];
        var line_idx := 0;
        while line_idx < n
            invariant 0 <= line_idx <= n
            invariant |curr_level| == line_idx
            invariant forall i :: 0 <= i < line_idx ==> |curr_level[i]| == m
        {
            curr_level := curr_level + [lines[1 + level_idx * n + line_idx]];
            line_idx := line_idx + 1;
        }
        levels := levels + [curr_level];
        level_idx := level_idx + 1;
    }
    levels
}

function int_to_string(n: nat): string
    ensures |int_to_string(n)| > 0
{
    if n == 0 then "0" else
        if n < 10 then [StringFromUnicodeView(n as int + '0' as int)] else
            int_to_string(n / 10) + [StringFromUnicodeView((n % 10) as int + '0' as int)]
}

function parse_dependency_line(s: string): (level: nat, parent: nat)
    requires s != "" && s[|s|-1] == '\n'
{
    var s_clean := s[..|s|-1];
    var parts := split_at_spaces(s_clean);
    (parse_nat(parts[0]), parse_nat(parts[1]))
}

function {:inline} StringFromUnicodeView(i: int): char
    requires 0 <= i < 0xD800 || (0xE000 <= i < 0x110000)
{
    i as char
}

function calculate_mst_cost(n: nat, m: nat, k: nat, w: nat, levels: seq<seq<string>>): nat
    requires |levels| == k
    requires forall i :: 0 <= i < k ==> |levels[i]| == n
    requires forall i :: 0 <= i < k ==> forall j :: 0 <= j < n ==> |levels[i][j]| == m
{
    if k == 0 then 0 else
        var total_cost := 0;
        var mst_parents := create_mst_parents(n, m, k, w, levels);
        var level := 0;
        while level < k
            invariant 0 <= level <= k
            invariant total_cost == calculate_mst_cost_partial(n, m, k, w, levels, mst_parents, level)
        {
            var parent := mst_parents[level];
            if parent > 0 {
                total_cost := total_cost + (w * count_differences(levels[level], levels[parent-1], n, m));
            }
            level := level + 1;
        }
        total_cost
}

function create_mst_parents(n: nat, m: nat, k: nat, w: nat, levels: seq<seq<string>>): seq<nat>
    requires |levels| == k
{
    if k == 0 then [] else
        var parents := [0];
        var in_tree := [0];
        var not_in_tree := iota(k);
        
        while |not_in_tree| > 0
            invariant |in_tree| + |not_in_tree| == k + 1
            invariant parents[in_tree[0]] == 0
            invariant forall i :: 1 <= i < |in_tree| ==> 1 <= parents[in_tree[i]] <= k
            invariant forall i :: 0 <= i < |not_in_tree| ==> 
                exists n_idx :: 0 <= n_idx < k && not_in_tree[i] == n_idx
            decreases |not_in_tree|
        {
            var u := not_in_tree[0];
            var min_edge_weight: nat := 1000000;
            var v_for_u: nat := 0;
            var i := 0;
            while i < |in_tree|
                invariant 0 <= i <= |in_tree|
                invariant min_edge_weight == find_min_weight_in_subtree(levels, n, m, w, u, in_tree, i, v_for_u)
            {
                var v := in_tree[i];
                var edge_weight := if v == 0 then w * (n * m) else w * count_differences(levels[u], levels[v-1], n, m);
                if edge_weight < min_edge_weight {
                    min_edge_weight := edge_weight;
                    v_for_u := v;
                }
                i := i + 1;
            }
            parents := parents + [v_for_u];
            in_tree := in_tree + [u];
            not_in_tree := not_in_tree[1..];
        }
        parents[1:]
}

function iota(n: nat): seq<nat>
    ensures |iota(n)| == n
    ensures forall i :: 0 <= i < n ==> iota(n)[i] == i
{
    if n == 0 then [] else iota(n-1) + [n-1]
}

function find_min_weight_in_subtree(levels: seq<seq<string>>, n: nat, m: nat, w: nat, u: nat, in_tree: seq<nat>, i: nat, current_v: nat): nat
    requires u < |levels|
    requires 0 <= i <= |in_tree|
    requires current_v <= |in_tree|
    decreases |in_tree| - i
{
    if i == 0 then 1000000 else
        var prev := find_min_weight_in_subtree(levels, n, m, w, u, in_tree, i-1, current_v);
        var v := in_tree[i-1];
        var edge_weight := if v == 0 then w * (n * m) else w * count_differences(levels[u], levels[v-1], n, m);
        if edge_weight < prev then edge_weight else prev
}

function calculate_mst_cost_partial(n: nat, m: nat, k: nat, w: nat, levels: seq<seq<string>>, parents: seq<nat>, processed_levels: nat): nat
    requires |levels| == k
    requires |parents| == k
    requires 0 <= processed_levels <= k
{
    var cost := 0;
    var l := 0;
    while l < processed_levels
        invariant 0 <= l <= processed_levels
        invariant cost == sum_mst_cost_partial(n, m, k, w, levels, parents, processed_levels, l)
    {
        if parents[l] > 0 {
            cost := cost + (w * count_differences(levels[l], levels[parents[l]-1], n, m));
        }
        l := l + 1;
    }
    cost
}

function sum_mst_cost_partial(n: nat, m: nat, k: nat, w: nat, levels: seq<seq<string>>, parents: seq<nat>, end_idx: nat, current_idx: nat): nat
    requires 0 <= current_idx <= end_idx <= k
    decreases end_idx - current_idx
{
    if current_idx == end_idx then 0 else
        var c := if parents[current_idx] > 0 then w * count_differences(levels[current_idx], levels[parents[current_idx]-1], n, m) else 0;
        c + sum_mst_cost_partial(n, m, k, w, levels, parents, end_idx, current_idx + 1)
}

function count_differences(level1: seq<string>, level2: seq<string>, n: nat, m: nat): nat
    requires |level1| == n
    requires |level2| == n
    requires forall i :: 0 <= i < n ==> |level1[i]| == m
    requires forall i :: 0 <= i < n ==> |level2[i]| == m
{
    if n == 0 then 0 else
        count_differences_row(level1[0], level2[0], m) + count_differences(level1[1..], level2[1..], n-1, m)
}

function count_differences_row(row1: string, row2: string, m: nat): nat
    requires |row1| == m
    requires |row2| == m
{
    if m == 0 then 0 else
        (if row1[0] != row2[0] then 1 else 0) + count_differences_row(row1[1..], row2[1..], m-1)
}

function concat(lines: seq<string>, i: nat): string
    requires 0 <= i <= |lines|
    decreases |lines| - i
{
    if i == |lines| then "" else lines[i] + concat(lines, i+1)
}

function is_valid_spanning_tree(result_lines: seq<string>, k: nat): bool
    requires |result_lines| == k + 1
{
    if k == 0 then true else
        var levels_visited := set();
        var parents := set();
        levels_visited := levels_visited + {0};
        var i := 1;
        while i < |result_lines|
            invariant 1 <= i <= |result_lines|
            invariant levels_visited == get_visited_levels(result_lines, i)
            invariant parents == get_parents_set(result_lines, i)
        {
            var (level, parent) := parse_dependency_line(result_lines[i]);
            levels_visited := levels_visited + {level};
            parents := parents + {parent};
            i := i + 1;
        }
        levels_visited == set(k) && parents <= set(k) && 0 in parents
}

function get_visited_levels(lines: seq<string>, i: nat): set<nat>
    requires 1 <= i <= |lines|
    decreases |lines| - i
{
    if i == 1 then set() else
        var (level, _) := parse_dependency_line(lines[i-1]);
        get_visited_levels(lines, i-1) + {level}
}

function get_parents_set(lines: seq<string>, i: nat): set<nat>
    requires 1 <= i <= |lines|
    decreases |lines| - i
{
    if i == 1 then set() else
        var (_, parent) := parse_dependency_line(lines[i-1]);
        get_parents_set(lines, i-1) + {parent}
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(result, stdin_input)
// </vc-spec>
// <vc-code>
{
    var lines := split_lines(stdin_input);
    var (n, m, k, w) := parse_first_line(lines[0]);
    assert k >= 1 && k <= 10;
    assert n >= 1 && n <= 10;
    assert m >= 1 && m <= 10;
    assert w >= 1 && w <= 1000;
    var levels := parse_levels(lines, n, m, k);
    assert |levels| == k;
    var mst_parents := create_mst_parents(n, m, k, w, levels);
    assert |mst_parents| == k;
    var total_cost := calculate_mst_cost(n, m, k, w, levels);
    var result_lines := [int_to_string(total_cost) + "\n"];
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant |result_lines| == i + 1
    {
        result_lines := result_lines + [int_to_string(i+1) + " " + int_to_string(mst_parents[i]) + "\n"];
        i := i + 1;
    }
    assert |result_lines| == k + 1;
    var result := concat(result_lines, 0);
    result
}
// </vc-code>

