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
/* helper modified by LLM (iteration 5): renamed local variable 'result' to 'res' to avoid scope conflict with return value */
fn can_turn_on_all_bulbs_exec(m: u8, buttons: &Vec<Vec<u8>>) -> bool
    requires
        m >= 1,
    ensures
        result == can_turn_on_all_bulbs(m as nat, buttons@.map(|i: int, button: Vec<u8>| button@.map(|j: int, bulb: u8| bulb as nat)))
{
    let mut present = Vec::new();
    let mut i = 0;
    while i < (m as usize) + 1
        invariant
            i <= (m as usize) + 1,
            present.len() == i,
    {
        present.push(false);
        i += 1;
    }

    for button in buttons {
        for bulb in button {
            let bulb_index = *bulb as usize;
            if bulb_index >= 1 && bulb_index <= m as usize {
                present[bulb_index] = true;
            }
        }
    }

    let mut j = 1;
    let mut res = true;
    while j <= m as usize
        invariant
            1 <= j <= (m as usize) + 1,
            res == (forall|k: int| 1 <= k < j ==> present@[k] == true),
    {
        if !present[j] {
            res = false;
            break;
        }
        j += 1;
    }
    res
}
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
    /* code modified by LLM (iteration 5): no changes needed, helper function call remains the same */
    if can_turn_on_all_bulbs_exec(m, &buttons) {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}