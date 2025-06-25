// Ex1

pub fn copyArr(a: &[int], l: int, r: int) -> (ret: Vec<int>)
    requires(
        0 <= l < r <= a.len()
    )
    ensures(|ret: Vec<int>|
        ret@ == a[l as usize..r as usize]
    )
{
}

// Ex2

// Ex3