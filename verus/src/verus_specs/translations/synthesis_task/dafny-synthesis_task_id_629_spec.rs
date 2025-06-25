use vstd::prelude::*;

verus! {

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}

pub fn FindEvenNumbers(arr: &[int]) -> (evenList: Seq<int>)
    requires()
    ensures(
        forall|i: int| 0 <= i < evenList.len() ==> IsEven(evenList[i]) && arr@.contains(evenList[i])
    )
    ensures(
        forall|i: int| 0 <= i < arr.len() && IsEven(arr[i]) ==> evenList.contains(arr[i])
    )
{
}

}