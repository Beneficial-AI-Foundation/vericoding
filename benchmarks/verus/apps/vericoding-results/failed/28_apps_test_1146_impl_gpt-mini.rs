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
{
/* helper modified by LLM (iteration 5): spec equivalence between union membership and existence */
spec fn union_contains_bulb_equiv(buttons: Seq<Seq<nat>>, bulb: nat) -> bool {
    union_of_all_bulbs(buttons).contains(bulb) <==> (exists|i: int, j: int| 0 <= i < buttons.len() && 0 <= j < buttons[i].len() && #[trigger] buttons[i][j] == bulb)
}

/* helper modified by LLM (iteration 5): spec lemma that having every bulb in the union implies can_turn_on_all_bulbs */
spec fn forall_membership_implies_can_turn_on(m: nat, buttons: Seq<Seq<nat>>) -> bool {
    (forall|k: int| 1 <= k <= m as int ==> union_of_all_bulbs(buttons).contains(k as nat)) ==> can_turn_on_all_bulbs(m, buttons)
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
    /* code modified by LLM (iteration 5): runtime check whether all bulbs 1..m appear across buttons, with a proof linking result to the spec predicate */
    let mut bulbs_on: Vec<bool> = Vec::new();
    let mut idx = 0usize;
    while idx < (m as usize)
    {
        bulbs_on.push(false);
        idx += 1;
    }

    let mut bi = 0usize;
    while bi < buttons.len()
    {
        let mut bj = 0usize;
        while bj < buttons[bi].len()
        {
            let v: u8 = buttons[bi][bj];
            if v >= 1 && v <= m {
                let pos = (v - 1) as usize;
                bulbs_on[pos] = true;
            }
            bj += 1;
        }
        bi += 1;
    }

    let mut all_on = true;
    let mut k = 0usize;
    while k < bulbs_on.len()
    {
        if !bulbs_on[k] {
            all_on = false;
            break;
        }
        k += 1;
    }

    if all_on {
        let result = String::from_str("YES");
        proof {
            let spec_buttons = buttons@.map(|i: int, button: Vec<u8>| button@.map(|j: int, bulb: u8| bulb as nat));
            assert(result@ == seq!['Y','E','S']);
            assert(can_turn_on_all_bulbs(m as nat, spec_buttons));
        }
        result
    } else {
        let result = String::from_str("NO");
        proof {
            let spec_buttons = buttons@.map(|i: int, button: Vec<u8>| button@.map(|j: int, bulb: u8| bulb as nat));
            assert(result@ == seq!['N','O']);
            assert(!can_turn_on_all_bulbs(m as nat, spec_buttons));
        }
        result
    }
}

// </vc-code>


}

fn main() {}