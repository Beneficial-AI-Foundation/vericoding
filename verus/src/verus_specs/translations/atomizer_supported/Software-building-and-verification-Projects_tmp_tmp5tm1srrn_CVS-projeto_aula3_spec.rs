// ATOM 
spec fn fib(n: nat) -> nat
{
  if n == 0 { 1 } else
  if n == 1 { 1 } else { fib((n-1) as nat) + fib((n-2) as nat) }
}

// SPEC 
pub fn Fib(n: nat) -> (r: nat)
    ensures(r == fib(n))
{
}

// 2.
// ATOM 
// 2.
pub enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> }
}

// ATOM 
spec fn add(l: List<int>) -> int {
    match l {
        List::Nil => 0,
        List::Cons { head: x, tail: xs } => x + add(*xs)
    }
}

// SPEC 
pub fn addImp(l: List<int>) -> (r: int)
    ensures(r == add(l))
{
}

// 3.
// SPEC 
// 3.
pub fn maxArray(arr: &[int]) -> (max: int)
    requires(arr.len() > 0)
    ensures(forall|i: int| 0 <= i < arr.len() ==> arr[i as usize] <= max)
    ensures(exists|x: int| 0 <= x < arr.len() && arr[x as usize] == max)
{
}

// 5.
// SPEC 
// 5.
pub fn maxArrayReverse(arr: &[int]) -> (max: int)
    requires(arr.len() > 0)
    ensures(forall|i: int| 0 <= i < arr.len() ==> arr[i as usize] <= max)
    ensures(exists|x: int| 0 <= x < arr.len() && arr[x as usize] == max)
{
}

// 6
// ATOM 
// 6
spec fn sum(n: nat) -> nat
{
    if n == 0 { 0 } else { n + sum((n-1) as nat) }
}

// SPEC 
pub fn sumBackwards(n: nat) -> (r: nat)
    ensures(r == sum(n))
{
}