// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>) -> bool {
    a.len() >= 1
}

spec fn can_be_divided(a: Seq<int>) -> bool
    recommends valid_input(a)
{
    a.len() % 2 == 1 && a[0] % 2 == 1 && a[a.len() - 1] % 2 == 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: String)
    requires 
        valid_input(a@.map(|i, x| x as int)),
    ensures 
        can_be_divided(a@.map(|i, x| x as int)) ==> result@ =~= seq!['Y', 'e', 's'],
        (!can_be_divided(a@.map(|i, x| x as int))) ==> result@ =~= seq!['N', 'o'],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed postcondition verification by ensuring proper spec-exec correspondence */
    let n = a.len();
    let a_spec = a@.map(|i, x| x as int);
    
    proof {
        assert(a_spec.len() == n);
    }
    
    if n % 2 == 0 {
        proof {
            assert(a_spec.len() % 2 == 0);
            assert(!can_be_divided(a_spec));
        }
        let result = "No".to_string();
        proof {
            assert(result@ =~= seq!['N', 'o']);
        }
        return result;
    }
    
    proof {
        assert(n % 2 == 1);
        assert(a_spec.len() % 2 == 1);
    }
    
    if a[0] % 2 == 0 {
        proof {
            assert(a@[0] == a[0]);
            assert(a_spec[0] == (a[0] as int));
            assert(a_spec[0] % 2 == 0);
            assert(!can_be_divided(a_spec));
        }
        let result = "No".to_string();
        proof {
            assert(result@ =~= seq!['N', 'o']);
        }
        return result;
    }
    
    proof {
        assert(a[0] % 2 == 1);
        assert(a_spec[0] == (a[0] as int));
        assert(a_spec[0] % 2 == 1);
    }
    
    if a[n - 1] % 2 == 0 {
        proof {
            assert(a@[n - 1] == a[n - 1]);
            assert(a_spec[a_spec.len() - 1] == (a[n - 1] as int));
            assert(a_spec[a_spec.len() - 1] % 2 == 0);
            assert(!can_be_divided(a_spec));
        }
        let result = "No".to_string();
        proof {
            assert(result@ =~= seq!['N', 'o']);
        }
        return result;
    }
    
    proof {
        assert(a[n - 1] % 2 == 1);
        assert(a_spec[a_spec.len() - 1] == (a[n - 1] as int));
        assert(a_spec.len() % 2 == 1);
        assert(a_spec[0] % 2 == 1);
        assert(a_spec[a_spec.len() - 1] % 2 == 1);
        assert(can_be_divided(a_spec));
    }
    let result = "Yes".to_string();
    proof {
        assert(result@ =~= seq!['Y', 'e', 's']);
    }
    result
}
// </vc-code>


}

fn main() {}