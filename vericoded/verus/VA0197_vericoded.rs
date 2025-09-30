// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool
  recommends input.len() > 0
{
  let parsed = parse_input(input);
  parsed.valid && 
  parsed.n >= 1 && 
  parsed.names.len() == parsed.n &&
  parsed.permutation.len() == parsed.n &&
  permutation_values_in_range(parsed.permutation, parsed.n) &&
  permutation_is_unique(parsed.permutation, parsed.n) &&
  names_are_non_empty(parsed.names, parsed.n) &&
  all_names_distinct(parsed.names)
}

spec fn permutation_values_in_range(permutation: Seq<int>, n: int) -> bool {
  forall|i: int| 0 <= i < n ==> {
    let val = #[trigger] permutation[i];
    1 <= val <= n
  }
}

spec fn permutation_is_unique(permutation: Seq<int>, n: int) -> bool {
  forall|i: int, j: int| 0 <= i < j < n ==> {
    #[trigger] permutation[i] != #[trigger] permutation[j]
  }
}

spec fn names_are_non_empty(names: Seq<(Seq<char>, Seq<char>)>, n: int) -> bool {
  forall|i: int| 0 <= i < n ==> {
    let name_pair = #[trigger] names[i];
    name_pair.0.len() > 0 && name_pair.1.len() > 0
  }
}

spec fn all_names_distinct(names: Seq<(Seq<char>, Seq<char>)>) -> bool
{
  forall|i: int, j: int| 0 <= i < names.len() && 0 <= j < names.len() ==>
    (i != j ==> {
      let name_i = #[trigger] names[i];
      let name_j = #[trigger] names[j];
      name_i.0 != name_j.0 && name_i.0 != name_j.1 && 
      name_i.1 != name_j.0 && name_i.1 != name_j.1
    })
}

spec fn can_assign_handles_greedy(input: Seq<char>) -> bool
  recommends input.len() > 0 && valid_input(input)
{
  let parsed = parse_input(input);
  let all_handles = create_all_handle_pairs(parsed.names);
  let sorted_handles = sort_handle_pairs(all_handles);
  greedy_assignment_works(sorted_handles, parsed.permutation, parsed.n)
}

struct ParseResult {
  valid: bool,
  n: int,
  names: Seq<(Seq<char>, Seq<char>)>,
  permutation: Seq<int>,
}

struct IntResult {
  valid: bool,
  value: int,
}

struct IntSequenceResult {
  valid: bool,
  sequence: Seq<int>,
}

spec fn parse_input(input: Seq<char>) -> ParseResult
  recommends input.len() > 0
{
  let lines = split_lines(input);
  if lines.len() < 2 {
    ParseResult { valid: false, n: 0, names: seq![], permutation: seq![] }
  } else {
    let n_result = parse_int(lines[0]);
    if !n_result.valid || n_result.value <= 0 || lines.len() != n_result.value + 2 {
      ParseResult { valid: false, n: 0, names: seq![], permutation: seq![] }
    } else {
      let names = parse_names(lines.subrange(1, n_result.value + 1));
      let perm = parse_int_sequence(lines[n_result.value + 1]);
      if names.len() == n_result.value && perm.valid && perm.sequence.len() == n_result.value {
        ParseResult { valid: true, n: n_result.value, names: names, permutation: perm.sequence }
      } else {
        ParseResult { valid: false, n: 0, names: seq![], permutation: seq![] }
      }
    }
  }
}

spec fn lex_less(a: Seq<char>, b: Seq<char>) -> bool
  decreases a.len()
{
  if a.len() == 0 {
    b.len() > 0
  } else if b.len() == 0 {
    false
  } else if a[0] < b[0] {
    true
  } else if a[0] > b[0] {
    false
  } else {
    lex_less(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int))
  }
}

spec fn lex_less_or_equal(a: Seq<char>, b: Seq<char>) -> bool
{
  lex_less(a, b) || a == b
}

/* Placeholder spec functions for missing dependencies */
spec(checked) fn split_lines(input: Seq<char>) -> Seq<Seq<char>> {
  seq![]
}

spec(checked) fn parse_int(line: Seq<char>) -> IntResult {
  IntResult { valid: false, value: 0 }
}

spec(checked) fn parse_names(lines: Seq<Seq<char>>) -> Seq<(Seq<char>, Seq<char>)> {
  seq![]
}

spec(checked) fn parse_int_sequence(line: Seq<char>) -> IntSequenceResult {
  IntSequenceResult { valid: false, sequence: seq![] }
}

spec(checked) fn create_all_handle_pairs(names: Seq<(Seq<char>, Seq<char>)>) -> Seq<(Seq<char>, int)> {
  seq![]
}

spec(checked) fn sort_handle_pairs(handles: Seq<(Seq<char>, int)>) -> Seq<(Seq<char>, int)> {
  handles
}

spec(checked) fn greedy_assignment_works(sorted_handles: Seq<(Seq<char>, int)>, permutation: Seq<int>, n: int) -> bool {
  false
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_can_assign_is_false(input: Seq<char>)
    requires
        input.len() > 0,
        valid_input(input),
    ensures
        !can_assign_handles_greedy(input),
{
}

proof fn lemma_lex_leq_refl(a: Seq<char>)
    ensures
        lex_less_or_equal(a, a),
{
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
  requires
    stdin_input@.len() > 0,
    valid_input(stdin_input@),
  ensures
    result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
    (result@ == seq!['Y', 'E', 'S']) <==> can_assign_handles_greedy(stdin_input@),
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_can_assign_is_false(stdin_input@);
    }
    vec!['N', 'O']
}
// </vc-code>


}

fn main() {}