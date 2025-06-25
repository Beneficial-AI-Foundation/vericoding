use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
pub enum Steps {
    One,
    Two,
}

pub spec fn stepSum(xs: Seq<Steps>) -> nat {
    if xs.len() == 0 { 
        0 
    } else { 
        (match xs[0] {
            Steps::One => 1,
            Steps::Two => 2,
        }) + stepSum(xs.subrange(1, xs.len() as int))
    }
}

pub open spec fn stepEndsAt(xs: Seq<Steps>, n: nat) -> bool {
    stepSum(xs) == n
}

pub open spec fn allEndAtN(ss: Set<Seq<Steps>>, n: nat) -> bool {
    forall |xs| ss.contains(xs) ==> stepEndsAt(xs, n)
}

proof fn stepBaseZero() 
    ensures exists |ss: Set<Seq<Steps>>| allEndAtN(ss, 0) && ss.len() == 0
{
}

proof fn stepBaseOne() 
    ensures exists |ss: Set<Seq<Steps>>| allEndAtN(ss, 1) && ss.len() == 1
{
}

proof fn stepBaseTwo() 
    ensures exists |ss: Set<Seq<Steps>>| allEndAtN(ss, 2) && ss.len() == 2
{
}

pub spec fn plusOne(x: Seq<Steps>) -> Seq<Steps> {
    seq![Steps::One].add(x)
}

pub spec fn addOne(ss: Set<Seq<Steps>>) -> Set<Seq<Steps>>
    ensures forall |x| ss.contains(x) ==> addOne(ss).contains(plusOne(x)),
    ensures addOne(ss) == Set::new(|x| ss.contains(x)).map(|x| plusOne(x)),
{
    Set::new(|x| ss.contains(x)).map(|x| plusOne(x))
}

proof fn SeqsNotEqualImplication<T>(xs: Seq<T>, ys: Seq<T>, someT: T)
    requires xs != ys
    ensures (exists |i: nat| i < xs.len() && i < ys.len() && xs[i as int] != ys[i as int]) || xs.len() < ys.len() || ys.len() < xs.len()
{
}

proof fn UnequalSeqs<T>(xs: Seq<T>, ys: Seq<T>, someT: T)
    requires xs != ys
    ensures seq![someT].add(xs) != seq![someT].add(ys)
{
}

proof fn plusOneNotIn(ss: Set<Seq<Steps>>, x: Seq<Steps>)
    requires !ss.contains(x)
    ensures !addOne(ss).contains(plusOne(x))
{
}

proof fn addOneSize(ss: Set<Seq<Steps>>)
    ensures addOne(ss).len() == ss.len()
{
}

proof fn addOneSum(ss: Set<Seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addOne(ss), sum+1)
{
}

proof fn endAtNPlus(ss: Set<Seq<Steps>>, sz: Set<Seq<Steps>>, sum: nat)
    requires allEndAtN(ss, sum)
    requires allEndAtN(sz, sum)
    ensures allEndAtN(ss.union(sz), sum)
{
}

pub spec fn plusTwo(x: Seq<Steps>) -> Seq<Steps> {
    seq![Steps::Two].add(x)
}

pub spec fn addTwo(ss: Set<Seq<Steps>>) -> Set<Seq<Steps>>
    ensures forall |x| ss.contains(x) ==> addTwo(ss).contains(plusTwo(x)),
    ensures addTwo(ss) == Set::new(|x| ss.contains(x)).map(|x| plusTwo(x)),
{
    Set::new(|x| ss.contains(x)).map(|x| plusTwo(x))
}

proof fn plusTwoNotIn(ss: Set<Seq<Steps>>, x: Seq<Steps>)
    requires !ss.contains(x)
    ensures !addTwo(ss).contains(plusTwo(x))
{
}

proof fn addTwoSize(ss: Set<Seq<Steps>>)
    ensures addTwo(ss).len() == ss.len()
{
}

proof fn addTwoSum(ss: Set<Seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addTwo(ss), sum+2)
{
}

proof fn setSizeAddition<T>(sx: Set<T>, sy: Set<T>, sz: Set<T>) 
    requires sx.disjoint(sy)
    requires sz == sx.union(sy)
    ensures sx.union(sy).len() == sx.len() + sy.len()
    ensures sz.len() == sx.len() + sy.len()
{
}

proof fn stepSetsAdd(i: nat, steps: &[nat]) 
    requires i >= 2
    requires steps.len() >= i+1
    requires forall |k: nat| k < i ==> exists |ss: Set<Seq<Steps>>| steps[k] == #[trigger] ss.len() && allEndAtN(ss, k)
    ensures exists |sp: Set<Seq<Steps>>| sp.len() == steps[i-1] + steps[i-2] && allEndAtN(sp, i)
{
}

pub fn climbStairs(n: nat) -> (count: nat)
    ensures exists |ss: Set<Seq<Steps>>| count == ss.len() && allEndAtN(ss, n)
{
}

pub fn Test() {
}

}