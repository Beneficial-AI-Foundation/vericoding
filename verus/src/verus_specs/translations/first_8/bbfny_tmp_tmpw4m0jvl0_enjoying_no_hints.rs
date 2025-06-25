//SPEC
pub fn MultipleReturns(x: int, y: int) -> (more: int, less: int)
    requires(0 < y)
    ensures(|result: (int, int)| result.1 < x < result.0)
{
}

//SPEC
pub fn Max(a: int, b: int) -> (c: int)
    ensures(|result: int| a <= result && b <= result)
    ensures(|result: int| a == result || b == result)
{
}

//ATOM
pub fn Testing() {
    let x = Max(3, 15);
}

//SPEC
spec fn max(a: int, b: int) -> int
{
}

//ATOM
pub fn Testing_prime() {
}

//ATOM
spec fn abs(x: int) -> int
{
    if x < 0 { -x } else { x }
}

//SPEC
pub fn Abs(x: int) -> (y: int)
    ensures(|result: int| result == abs(x))
{
}

//ATOM
pub fn m(n: nat) {
    let mut i = 0;
    while i != n {
        i = i + 1;
    }
}

//ATOM
spec fn fib(n: nat) -> nat
    decreases(n)
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fib((n - 1) as nat) + fib((n - 2) as nat)
    }
}

//SPEC
pub fn Find(a: &[int], key: int) -> (index: int)
    ensures(|result: int| 0 <= result ==> result < a.len() && a[result] == key)
    ensures(|result: int| result < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != key)
{
}

//SPEC
pub fn FindMax(a: &[int]) -> (i: int)
    requires(a.len() >= 1)
    ensures(|result: int| 0 <= result < a.len())
    ensures(|result: int| forall|k: int| 0 <= k < a.len() ==> a[k] <= a[result])
{
}

//ATOM
spec fn sorted(a: &[int]) -> bool
{
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] < a[k]
}

//ATOM
spec fn sorted_prime(a: Option<&[int]>) -> bool
{
    forall|j: int, k: int| a.is_some() && 0 <= j < k < a.unwrap().len() ==> a.unwrap()[j] <= a.unwrap()[k]
}