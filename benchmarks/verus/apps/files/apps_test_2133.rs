// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_tree_input(input: Seq<char>) -> bool {
  let lines = split_lines(input);
  lines.len() >= 2 &&
  {
    let n = parse_int(lines[0]);
    n >= 1 && n <= 200000 &&
    lines.len() == n + 1 &&
    valid_color_line(lines[1], n) &&
    valid_edge_lines(lines.subrange(2, lines.len() as int), n) &&
    {
      let edges = Seq::new((lines.len() - 2) as nat, |i: int| {
        let edge = parse_int_seq(lines[i + 2]);
        (edge[0], edge[1])
      });
      is_valid_tree(n, edges)
    }
  }
}

spec fn valid_color_line(line: Seq<char>, n: int) -> bool {
  let colors = parse_int_seq(line);
  colors.len() == n &&
  forall|i: int| #![trigger colors[i]] 0 <= i < colors.len() ==> colors[i] == 0 || colors[i] == 1
}

spec fn valid_edge_lines(lines: Seq<Seq<char>>, n: int) -> bool {
  lines.len() == n - 1 &&
  forall|i: int| #![trigger lines[i]] 0 <= i < lines.len() ==> {
    let edge = parse_int_seq(lines[i]);
    edge.len() == 2 && 
    1 <= edge[0] <= n && 
    1 <= edge[1] <= n && 
    edge[0] != edge[1]
  }
}

spec fn is_valid_tree(n: int, edges: Seq<(int, int)>) -> bool {
  n >= 1 &&
  edges.len() == n - 1 &&
  is_connected(n, edges) &&
  (forall|e: (int, int)| edges.contains(e) ==> 1 <= e.0 <= n && 1 <= e.1 <= n && e.0 != e.1) &&
  no_duplicate_edges(edges)
}

spec fn is_connected(n: int, edges: Seq<(int, int)>) -> bool {
  true
}

spec fn no_duplicate_edges(edges: Seq<(int, int)>) -> bool {
  forall|i: int, j: int| #![trigger edges[i], edges[j]] 0 <= i < j < edges.len() ==> 
    edges[i] != edges[j] && 
    (edges[i].0, edges[i].1) != (edges[j].1, edges[j].0)
}

spec fn valid_integer_output(output: Seq<char>) -> bool {
  let trimmed = trim_whitespace(output);
  trimmed.len() > 0 &&
  forall|c: char| trimmed.contains(c) ==> '0' <= c <= '9'
}

spec fn all_same_color(colors: Seq<int>) -> bool {
  colors.len() > 0 ==> forall|i: int| #![trigger colors[i]] 0 <= i < colors.len() ==> colors[i] == colors[0]
}

spec fn parse_input(input: Seq<char>) -> (int, Seq<int>, Seq<(int, int)>) {
  let lines = split_lines(input);
  let n = parse_int(lines[0]);
  let colors = parse_int_seq(lines[1]);
  let edges = Seq::new((lines.len() - 2) as nat, |i: int| {
    let edge = parse_int_seq(lines[i + 2]);
    (edge[0], edge[1])
  });
  (n, colors, edges)
}

spec fn parse_output(output: Seq<char>) -> int {
  parse_int(trim_whitespace(output))
}

spec fn compute_min_paint_ops(n: int, colors: Seq<int>, edges: Seq<(int, int)>) -> int {
  if all_same_color(colors) {
    0
  } else {
    let components = build_same_color_components(colors, edges);
    let component_graph = build_component_graph(components, colors, edges);
    (tree_diameter(component_graph) + 1) / 2
  }
}

spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>> { Seq::empty() }
spec fn parse_int(line: Seq<char>) -> int { 0 }
spec fn parse_int_seq(line: Seq<char>) -> Seq<int> { Seq::empty() }
spec fn trim_whitespace(output: Seq<char>) -> Seq<char> { output }
spec fn build_same_color_components(colors: Seq<int>, edges: Seq<(int, int)>) -> Seq<Seq<int>> { Seq::empty() }
spec fn build_component_graph(components: Seq<Seq<int>>, colors: Seq<int>, edges: Seq<(int, int)>) -> Seq<(int, int)> { Seq::empty() }
spec fn tree_diameter(graph: Seq<(int, int)>) -> int { 0 }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
  requires 
    stdin_input@ .len() > 0,
    valid_tree_input(stdin_input@),
  ensures 
    output@ .len() > 0,
    valid_integer_output(output@),
    ({
      let result = parse_output(output@);
      result >= 0
    }),
    ({
      let (n, colors, edges) = parse_input(stdin_input@);
      n >= 1 ==> {
        let result = parse_output(output@);
        result <= n
      }
    }),
    ({
      let (n, colors, edges) = parse_input(stdin_input@);
      all_same_color(colors) ==> parse_output(output@) == 0
    }),
    ({
      let (n, colors, edges) = parse_input(stdin_input@);
      n == 1 ==> parse_output(output@) == 0
    }),
    ({
      let (n, colors, edges) = parse_input(stdin_input@);
      is_valid_tree(n, edges) && n >= 1
    }),
    ({
      let (n, colors, edges) = parse_input(stdin_input@);
      let result = parse_output(output@);
      result == compute_min_paint_ops(n, colors, edges)
    }),
// </vc-spec>
// <vc-code>
{
  // impl-start
  assume(false);
  unreached()
  // impl-end
}
// </vc-code>


}

fn main() {}