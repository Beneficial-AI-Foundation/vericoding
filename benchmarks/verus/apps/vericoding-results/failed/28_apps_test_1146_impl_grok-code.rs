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
/* helper modified by LLM (iteration 4): removed invalid spec! macro calls */
fn compute_union(buttons: &Vec<Vec<u8>>) -> (tracked result: Set<nat>)
    ensures
        result == union_of_all_bulbs(buttons@.map(|i: int, b: Vec<u8>| b@.map(|j: int, bu: u8| bu as nat)))
{
    let tracked mut set: Set<nat> = Set::empty();
    let mut i: usize = 0;
    while i < buttons.len()
        invariant
            0 <= i@ <= buttons.len(),
            set =~= Set::new(|bulb: nat| 
                exists|i_: int, j: int| 
                    0 <= i_ < i@ && 
                    0 <= j < buttons@[i_].len() && 
                    #[trigger] buttons@[i_][j] == bulb
            )
    {
        let mut j: usize = 0;
        while j < buttons[i].len()
            invariant
                0 <= j@ <= buttons@[i@].len(),
                set =~= Set::new(|bulb: nat| 
                    (exists|i_: int, j_: int| 
                        0 <= i_ < i@ && 
                        0 <= j_ < buttons@[i_].len() && 
                        buttons@[i_][j_] == bulb) ||
                    (exists|j_: int| 
                        0 <= j_ < j@ && 
                        #[trigger] buttons@[i@][j_] == bulb)
                )
        {
            let bulb: u8 = buttons[i][j];
            let ghost bulb_nat: nat = bulb as nat;
            set = set.insert(bulb_nat);
            j += 1;
        }
        i += 1;
    }
    set
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
/* code modified by LLM (iteration 4): removed spec! to fix compilation */
{
    let tracked union: Set<nat> = compute_union(&buttons);
    let ghost all_covered: bool = union.finite() && union.len() == m as nat;
    if *all_covered {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}