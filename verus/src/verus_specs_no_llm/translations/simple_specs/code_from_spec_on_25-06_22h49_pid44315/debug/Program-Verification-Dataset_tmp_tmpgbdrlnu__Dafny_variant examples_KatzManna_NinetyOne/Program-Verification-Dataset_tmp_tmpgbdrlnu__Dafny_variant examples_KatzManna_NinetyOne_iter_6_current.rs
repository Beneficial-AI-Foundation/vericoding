use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) -> (z: int)
    ensures
        proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91
{
    if x > 101 {
        let result = x - 10;
        proof {
            if proveFunctionalPostcondition {
                assert(result == x - 10);
                assert(x > 101);
                assert(result == if x > 101 then x-10 else 91);
            }
        }
        result
    } else {
        let result = 91;
        proof {
            if proveFunctionalPostcondition {
                assert(result == 91);
                assert(!(x > 101));
                assert(result == if x > 101 then x-10 else 91);
            }
        }
        result
    }
}

}