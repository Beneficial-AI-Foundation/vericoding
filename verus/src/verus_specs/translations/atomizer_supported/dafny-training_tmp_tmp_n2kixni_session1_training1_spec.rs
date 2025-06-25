use vstd::prelude::*;

verus! {

pub fn abs(x: int) -> (y: int)
    ensures(true)
{
}

pub fn foo(x: int) 
    requires(x >= 0)
{
}

pub fn max(x: int, y: int) -> (m: int)
    requires(true)
    ensures(true)
{
}

pub fn ex1(n: int)
    requires(true)
    ensures(true)
{
}

pub fn foo2() 
    ensures(false)
{
}

pub fn find(a: Seq<int>, key: int) -> (index: int)
    requires(true)
    ensures(true)
{
}

pub fn isPalindrome(a: Seq<char>) -> (b: bool) 
{
}

pub open spec fn sorted(a: Seq<int>) -> bool
{
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] <= a[k]
}

pub fn unique(a: Seq<int>) -> (b: Seq<int>) 
    requires(sorted(a))
    ensures(true)
{
}

pub fn Main() {
}

}