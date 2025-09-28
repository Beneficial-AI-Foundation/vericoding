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
/* helper modified by LLM (iteration 5): Added helper for string creation */
fn create_yes_string() -> (result: String)
    ensures result@ == seq!['Y', 'E', 'S']
{
    let mut s = String::new();
    s.push('Y');
    s.push('E');
    s.push('S');
    s
}

fn create_no_string() -> (result: String)
    ensures result@ == seq!['N', 'O']
{
    let mut s = String::new();
    s.push('N');
    s.push('O');
    s
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
    /* code modified by LLM (iteration 5): Fixed compilation by using usize instead of nat in exec code */
    let mut all_bulbs: Set<u8> = Set::empty();
    let mut i = 0;
    
    while i < buttons.len()
        invariant
            0 <= i <= buttons.len(),
            all_bulbs == Set::new(|bulb: u8|
                exists|row: int, col: int|
                    0 <= row < i &&
                    0 <= col < buttons@[row].len() &&
                    #[trigger] buttons@[row][col] == bulb as nat
            ),
        decreases buttons.len() - i
    {
        let mut j = 0;
        
        while j < buttons[i].len()
            invariant
                0 <= j <= buttons@[i as int].len(),
                all_bulbs == Set::new(|bulb: u8|
                    (exists|row: int, col: int|
                        0 <= row < i &&
                        0 <= col < buttons@[row].len() &&
                        #[trigger] buttons@[row][col] == bulb as nat) ||
                    (exists|col: int|
                        0 <= col < j &&
                        #[trigger] buttons@[i as int][col] == bulb as nat)
                ),
            decreases buttons@[i as int].len() - j
        {
            all_bulbs = all_bulbs.insert(buttons[i][j]);
            j += 1;
        }
        i += 1;
    }
    
    proof {
        let button_seq = buttons@.map(|i: int, button: Vec<u8>| button@.map(|j: int, bulb: u8| bulb as nat));
        let union_set = union_of_all_bulbs(button_seq);
        
        assert forall|bulb: nat| union_set.contains(bulb) <==> all_bulbs.contains(bulb as u8) by {
            if union_set.contains(bulb) {
                assert(exists|i: int, j: int| 
                    0 <= i < button_seq.len() && 
                    0 <= j < button_seq[i].len() && 
                    button_seq[i][j] == bulb);
            }
            if all_bulbs.contains(bulb as u8) {
                assert(exists|row: int, col: int|
                    0 <= row < buttons.len() &&
                    0 <= col < buttons@[row].len() &&
                    buttons@[row][col] == bulb);
            }
        };
        
        assert(union_set.finite());
        assert(union_set.len() == all_bulbs.len());
    }
    
    if all_bulbs.len() == m as usize {
        create_yes_string()
    } else {
        create_no_string()
    }
}
// </vc-code>


}

fn main() {}