// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
spec fn valid_input(n: nat, m: nat, buttons: Seq<Seq<nat>>) -> bool {
    buttons.len() == n &&
    n >= 1 && m >= 1 &&
    forall|i: int| 0 <= i < n ==> 
        #[trigger] buttons[i].len() >= 0 &&
        forall|j: int| 0 <= j < buttons[i].len() ==> 1 <= #[trigger] buttons[i][j] <= m
}

spec fn union_of_all_bulbs(buttons: Seq<Seq<nat>>) -> Set<nat> {
    Set::new(|bulb: nat| 
        exists|i: int, j: int| 
            0 <= i < buttons.len() && 
            0 <= j < buttons[i].len() && 
            #[trigger] buttons[i][j] == bulb
    )
}

spec fn can_turn_on_all_bulbs(m: nat, buttons: Seq<Seq<nat>>) -> bool {
    union_of_all_bulbs(buttons).finite() && union_of_all_bulbs(buttons).len() == m
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: u8, m: u8, buttons: Vec<Vec<u8>>) -> (result: String)
    requires
        valid_input(n as nat, m as nat, buttons@.map(|i: int, button: Vec<u8>| button@.map(|j: int, bulb: u8| bulb as nat))),
    ensures
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        (result@ == seq!['Y', 'E', 'S']) <==> can_turn_on_all_bulbs(m as nat, buttons@.map(|i: int, button: Vec<u8>| button@.map(|j: int, bulb: u8| bulb as nat)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches in invariants and conditionals */
    let mut seen_bulbs: Set<u8> = Set::empty();
    let mut i: usize = 0;
    
    while i < buttons.len()
        invariant
            i <= buttons.len(),
            seen_bulbs.finite(),
            forall|bulb: u8| seen_bulbs.contains(bulb) ==>
                exists|ii: int, jj: int| 
                    0 <= ii < i && 
                    0 <= jj < buttons@[ii].len() && 
                    buttons@[ii][jj] == bulb,
            valid_input(n as nat, m as nat, buttons@.map(|i: int, button: Vec<u8>| button@.map(|j: int, bulb: u8| bulb as nat))),
    {
        let mut j: usize = 0;
        while j < buttons[i].len()
            invariant
                j <= buttons[i].len(),
                i < buttons.len(),
                seen_bulbs.finite(),
                forall|bulb: u8| seen_bulbs.contains(bulb) ==>
                    exists|ii: int, jj: int| 
                        (0 <= ii < i && 0 <= jj < buttons@[ii].len() && buttons@[ii][jj] == bulb) ||
                        (ii == i as int && 0 <= jj < j as int && buttons@[i as int][jj] == bulb),
                valid_input(n as nat, m as nat, buttons@.map(|i: int, button: Vec<u8>| button@.map(|j: int, bulb: u8| bulb as nat))),
        {
            let bulb = buttons[i][j];
            seen_bulbs = seen_bulbs.insert(bulb);
            j = j + 1;
        }
        i = i + 1;
    }
    
    if seen_bulbs.len() == m as nat {
        let mut result = String::new();
        result.push_str("YES");
        return result;
    } else {
        let mut result = String::new();
        result.push_str("NO");
        return result;
    }
}
// </vc-code>


}

fn main() {}