// SPEC 
pub fn Max(x: nat, y: nat) -> r: nat
    requires()
    ensures(r >= x && r >= y)
    ensures(r == x || r == y)
{
}

// SPEC 
pub fn Test()
    requires()
    ensures()
{
}

// SPEC 
pub fn m1(x: int, y: int) -> z: int
    requires(0 < x < y)
    ensures(z >= 0 && z <= y && z != x)
{
}

// ATOM 
spec fn fib(n: nat) -> nat
{
    if n == 0 { 1 } else
    if n == 1 { 1 } else
    fib(n - 1) + fib(n - 2)
}

// SPEC 
pub fn Fib(n: nat) -> r: nat
    requires()
    ensures(r == fib(n))
{
}

// ATOM 
enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> }
}

// ATOM 
spec fn add(l: List<int>) -> int
{
    match l {
        List::Nil => 0,
        List::Cons { head: x, tail: xs } => x + add(*xs)
    }
}

// SPEC 
pub fn addImp(l: List<int>) -> s: int
    requires()
    ensures(s == add(l))
{
}

// SPEC 
pub fn MaxA(a: &[int]) -> m: int
    requires(a.len() > 0)
    ensures(forall|i: usize| 0 <= i < a.len() ==> a[i] <= m)
    ensures(exists|i: usize| 0 <= i < a.len() && a[i] == m)
{
}