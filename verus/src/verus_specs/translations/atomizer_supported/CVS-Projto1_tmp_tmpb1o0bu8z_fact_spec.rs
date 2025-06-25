// ATOM 
pub fn fact(n: nat) -> nat
{
}

// ATOM 
pub fn factAcc(n: nat, a: int) -> int
{
}

// ATOM 
pub fn factAlt(n: nat) -> int
{
}

// ATOM 
pub fn factAcc_correct(n: nat, a: int)
    ensures(factAcc(n, a) == a * fact(n))
{
}

// ATOM 
pub fn factAlt_correct(n: nat)
    ensures(factAlt(n) == fact(n))
{
}

// ATOM 
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

// ATOM 
pub fn length<T>(l: List<T>) -> nat
{
}

pub fn length_non_neg<T>(l: List<T>)
    ensures(length(l) >= 0)
{
}

// ATOM 
pub fn lengthTL<T>(l: List<T>, acc: nat) -> nat
{
}

pub fn lengthTL_aux<T>(l: List<T>, acc: nat)
    ensures(lengthTL(l, acc) == acc + length(l))
{
}

// ATOM 
pub fn lengthEq<T>(l: List<T>)
    ensures(length(l) == lengthTL(l, 0))
{
}