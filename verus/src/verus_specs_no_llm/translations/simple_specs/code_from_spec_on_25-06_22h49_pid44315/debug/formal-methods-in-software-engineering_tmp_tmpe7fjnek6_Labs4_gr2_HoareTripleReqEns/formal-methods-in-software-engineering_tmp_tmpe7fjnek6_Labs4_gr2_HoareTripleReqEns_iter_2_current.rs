use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn HoareTripleReqEns(i: int, k: int) -> (k': int)
	// (| k == i*i |) k := k + 2 * i +1; (| k = (i+1)*(i+1) |)
    requires
        k == i*i
    ensures
        k' == (i+1)*(i+1)
{
    assert((i+1)*(i+1) == i*i + 2*i + 1);
    k + 2 * i + 1
}

}