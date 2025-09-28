// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    100 <= n <= 999
}

spec fn contains_seven(n: int) -> bool
    recommends valid_input(n)
{
    (n % 10) == 7 || ((n / 10) % 10) == 7 || (n / 100) == 7
}

spec fn valid_output(result: Seq<char>) -> bool {
    result == "Yes\n"@ || result == "No\n"@
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures 
        valid_output(result@) &&
        ((result@ == "Yes\n"@) <==> contains_seven(n as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Manually construct vectors with proper sequence assertions */
    let digit1 = n % 10;
    let digit2 = (n / 10) % 10;
    let digit3 = n / 100;
    
    let result = if digit1 == 7 || digit2 == 7 || digit3 == 7 {
        proof {
            assert(digit1 as int == (n as int) % 10);
            assert(digit2 as int == ((n as int) / 10) % 10);
            assert(digit3 as int == (n as int) / 100);
            assert((digit1 == 7) ==> ((n as int) % 10 == 7));
            assert((digit2 == 7) ==> (((n as int) / 10) % 10 == 7));
            assert((digit3 == 7) ==> ((n as int) / 100 == 7));
            assert(contains_seven(n as int));
        }
        let mut v = Vec::new();
        v.push('Y');
        v.push('e');
        v.push('s');
        v.push('\n');
        proof {
            assert(v@.len() == 4);
            assert(v@[0] == 'Y');
            assert(v@[1] == 'e');
            assert(v@[2] == 's');
            assert(v@[3] == '\n');
            assert(v@ =~= seq!['Y', 'e', 's', '\n']);
        }
        v
    } else {
        proof {
            assert(digit1 as int == (n as int) % 10);
            assert(digit2 as int == ((n as int) / 10) % 10);
            assert(digit3 as int == (n as int) / 100);
            assert(digit1 != 7);
            assert(digit2 != 7);
            assert(digit3 != 7);
            assert((n as int) % 10 != 7);
            assert(((n as int) / 10) % 10 != 7);
            assert((n as int) / 100 != 7);
            assert(!contains_seven(n as int));
        }
        let mut v = Vec::new();
        v.push('N');
        v.push('o');
        v.push('\n');
        proof {
            assert(v@.len() == 3);
            assert(v@[0] == 'N');
            assert(v@[1] == 'o');
            assert(v@[2] == '\n');
            assert(v@ =~= seq!['N', 'o', '\n']);
        }
        v
    };
    
    proof {
        if digit1 == 7 || digit2 == 7 || digit3 == 7 {
            assert(result@ =~= seq!['Y', 'e', 's', '\n']);
            assert("Yes\n"@ =~= seq!['Y', 'e', 's', '\n']);
            assert(result@ =~= "Yes\n"@);
            assert(valid_output(result@));
        } else {
            assert(result@ =~= seq!['N', 'o', '\n']);
            assert("No\n"@ =~= seq!['N', 'o', '\n']);
            assert(result@ =~= "No\n"@);
            assert(valid_output(result@));
        }
        assert((result@ =~= "Yes\n"@) <==> contains_seven(n as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}