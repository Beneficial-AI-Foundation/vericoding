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
        assert(proveFunctionalPostcondition ==> result == (if x > 101 then x-10 else 91));
        result
    } else {
        let result = 91;
        assert(proveFunctionalPostcondition ==> result == (if x > 101 then x-10 else 91));
        result
    }
}

}