use vstd::prelude::*;

verus! {
spec fn sum(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(0, |acc: int, x| acc + x)
}
// pure-end

spec fn product(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(1, |acc: int, x| acc * x)
}
// pure-end

proof fn sum_bound(numbers: Seq<u32>)
    // post-conditions-start
    ensures
        sum(numbers) <= numbers.len() * u32::MAX,
    decreases numbers.len(),
    // post-conditions-end
{
    // impl-start
    if numbers.len() == 0 {
    } else {
        sum_bound(numbers.drop_last());
    }
    // impl-end
}
// pure-end

fn sum_product(numbers: Vec<u32>) -> (result: (u64, Option<u32>))
    // pre-conditions-start
    requires
        numbers.len() < u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.0 == sum(numbers@),
        result.1 matches Some(v) ==> v == product(numbers@),
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

}
fn main() {}
