use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountLessThan(numbers: Set<int>, threshold: int) -> (count: int)
    ensures
        count == (Set::new(|i: int| numbers.contains(i) && i < threshold)).len()
{
    let mut count = 0;
    let mut remaining = numbers;
    
    while remaining.len() > 0
        invariant
            count + (Set::new(|i: int| remaining.contains(i) && i < threshold)).len() == 
                (Set::new(|i: int| numbers.contains(i) && i < threshold)).len(),
            remaining.subset_of(numbers)
    {
        let elem = remaining.choose();
        remaining = remaining.remove(elem);
        if elem < threshold {
            count = count + 1;
        }
    }
    
    count
}

}