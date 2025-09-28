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
proof fn union_set_satisfies_property(m: nat, buttons: Seq<Seq<nat>>, bulb: nat)
    requires
        can_turn_on_all_bulbs(m, buttons),
    ensures
        1 <= bulb <= m ==> exists|i: int, j: int| 
            0 <= i < buttons.len() && 
            0 <= j < buttons[i].len() && 
            buttons[i][j] == bulb
{
    assert(union_of_all_bulbs(buttons).finite());
    assert(union_of_all_bulbs(buttons).len() == m);
    assert(forall|b: nat| union_of_all_bulbs(buttons).contains(b) <==> 
        exists|i: int, j: int| 0 <= i < buttons.len() && 0 <= j < buttons[i].len() && buttons[i][j] == b);
    assert(forall|b: nat| 1 <= b <= m ==> union_of_all_bulbs(buttons).contains(b));
}

spec fn button_covers_bulb(row: int, col: int, button_row: Seq<nat>, bulb: nat) -> bool {
    0 <= col < button_row.len() && button_row[col] == bulb
}

proof fn find_bulb_correctness(buttons: Seq<Seq<nat>>, bulb: nat, idx: int)
    requires
        1 <= bulb <= buttons.len() as nat,
        0 <= idx < buttons.len(),
        exists|col: int| button_covers_bulb(idx, col, buttons[idx], bulb),
    ensures
        exists|col: int| 0 <= col < buttons[idx].len() && buttons[idx][col] == bulb
{
}

/* helper modified by LLM (iteration 5): Added buttons_seq parameter to union_set_satisfies_property call */
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
    /* code modified by LLM (iteration 5): Fixed compilation error by passing buttons_seq to helper function */
    proof {
        let buttons_seq: Seq<Seq<nat>> = buttons@.map(|i: int, button: Vec<u8>| button@.map(|j: int, bulb: u8| bulb as nat));
        union_set_satisfies_property(m as nat, buttons_seq, 0);
    }
    
    let buttons_seq_ghost = buttons@.map(|i: int, button: Vec<u8>| button@.map(|j: int, bulb: u8| bulb));
    
    let mut all_bulbs_covered: bool = true;
    let mut bulb: u8 = 1;
    
    while bulb <= m
        invariant
            bulb <= m + 1,
            all_bulbs_covered == (forall|b: nat| 1 <= b < bulb as nat ==> 
                exists|i: int, j: int| 0 <= i < buttons_seq_ghost.len() && 0 <= j < buttons_seq_ghost[i].len() && buttons_seq_ghost[i][j] as nat == b)
    {
        let mut found: bool = false;
        let mut i: usize = 0;
        
        while i < buttons.len()
            invariant
                i <= buttons.len(),
                found == (exists|row: int| 0 <= row < i as int && 
                    exists|col: int| 0 <= col < buttons_seq_ghost[row].len() && buttons_seq_ghost[row][col] as nat == bulb as nat)
        {
            let mut j: usize = 0;
            let button_row = &buttons[i];
            
            while j < button_row.len()
                invariant
                    j <= button_row.len(),
                    found == (exists|col: int| 0 <= col < j as int && buttons_seq_ghost[i as int][col] as nat == bulb as nat)
            {
                if button_row[j] == bulb {
                    found = true;
                    break;
                }
                j += 1;
            }
            
            if found {
                break;
            }
            i += 1;
        }
        
        if !found {
            all_bulbs_covered = false;
            break;
        }
        bulb += 1;
    }
    
    if all_bulbs_covered {
        String::from_str("YES")
    } else {
        String::from_str("NO")
    }
}
// </vc-code>


}

fn main() {}