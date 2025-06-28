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
        assert(proveFunctionalPostcondition ==> result == x - 10);
        assert(proveFunctionalPostcondition ==> (if x > 101 then x-10 else 91) == x - 10);
        result
    } else {
        let result = 91;
        assert(proveFunctionalPostcondition ==> result == 91);
        assert(proveFunctionalPostcondition ==> (if x > 101 then x-10 else 91) == 91);
        result
    }
}

}