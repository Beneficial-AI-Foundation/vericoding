/* numpy.bincount: Count number of occurrences of each value in array of non-negative ints.

    Count number of occurrences of each value in array of non-negative ints.
    The number of bins (of size 1) is one larger than the largest value in x.
    Each bin gives the number of occurrences of its index value in x.
    
    This function takes a 1D array of non-negative integers and returns
    an array where the i-th element is the count of how many times the
    value i appears in the input array.

    Specification: numpy.bincount returns count of occurrences of each value.

    Precondition: All values in x are non-negative and ≤ max_val
    Postcondition: result[i] = count of occurrences of value i in x */

use vstd::prelude::*;

verus! {
spec fn count_occurrences(seq: Seq<usize>, val: usize) -> int {
    seq.filter(|x: usize| x == val).len() as int
}
fn numpy_bincount(x: &Vec<usize>, max_val: usize) -> (result: Vec<usize>)
    requires
        forall|i: int| 0 <= i < x.len() ==> x[i] <= max_val,
    ensures
        result.len() == max_val + 1,
        forall|val: int| 0 <= val <= max_val ==> result[val] == count_occurrences(x@, val as usize),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}

fn main() {}