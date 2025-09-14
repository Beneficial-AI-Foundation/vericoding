// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, a: int, m: int, shots: Seq<int>) -> bool {
    n > 0 && k > 0 && a > 0 && m > 0 && shots.len() == m &&
    (forall|i: int| 0 <= i < shots.len() ==> 1 <= shots[i] <= n)
}

spec fn collect_hit_cells(shots: Seq<int>, num_shots: int) -> Set<int> {
    if num_shots <= 0 || num_shots > shots.len() {
        Set::empty()
    } else {
        Set::empty().insert(shots[0]).union(collect_hit_cells(shots.subrange(1, shots.len() as int), num_shots - 1))
    }
}

spec fn can_place_ships_func(n: int, k: int, a: int, shots: Seq<int>, num_shots: int) -> bool {
    let hit_cells = collect_hit_cells(shots, num_shots);
    greedy_ship_placement(n, k, a, hit_cells) >= k
}

spec fn greedy_ship_placement(n: int, k: int, a: int, hit_cells: Set<int>) -> int {
    greedy_place_ships_from_position(1, n, k, a, hit_cells)
}

spec fn greedy_place_ships_from_position(pos: int, n: int, k: int, a: int, hit_cells: Set<int>) -> int
    decreases n - pos + 1, k
{
    if pos > n || k == 0 {
        0
    } else if pos + a - 1 <= n && (forall|cell: int| pos <= cell <= pos + a - 1 ==> !hit_cells.contains(cell)) {
        1 + greedy_place_ships_from_position(pos + a + 1, n, k - 1, a, hit_cells)
    } else {
        greedy_place_ships_from_position(pos + 1, n, k, a, hit_cells)
    }
}

spec fn is_natural_number_string(s: Seq<char>) -> bool {
    s.len() > 0 && s[0] != '0' && (forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9')
}

spec fn parse_input_spec(input: Seq<char>) -> Seq<Seq<char>> {
    seq![]
}

spec fn parse_three_ints_spec(line: Seq<char>) -> (int, int, int) {
    (1, 1, 1)
}

spec fn parse_int_spec(line: Seq<char>) -> int {
    0
}

spec fn parse_int_array_spec(line: Seq<char>) -> Seq<int> {
    seq![]
}

spec fn int_to_string_spec(value: int) -> Seq<char> {
    seq!['1']
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}