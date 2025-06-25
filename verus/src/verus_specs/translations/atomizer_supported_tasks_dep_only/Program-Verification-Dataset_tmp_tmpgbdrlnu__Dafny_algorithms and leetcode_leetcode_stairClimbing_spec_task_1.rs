pub enum Steps {
    One,
    Two,
}

pub spec fn stepSum(xs: Seq<Steps>) -> nat {
    if xs.len() == 0 { 0 } else {
        match xs[0] {
            Steps::One => 1,
            Steps::Two => 2,
        } + stepSum(xs.subrange(1, xs.len() as int))
    }
}

pub spec fn stepEndsAt(xs: Seq<Steps>, n: nat) -> bool {
    stepSum(xs) == n
}

pub spec fn allEndAtN(ss: Set<Seq<Steps>>, n: nat) -> bool {
    forall |xs| ss.contains(xs) ==> stepEndsAt(xs, n)
}

pub proof fn stepBaseZero()
    ensures exists |ss: Set<Seq<Steps>>| allEndAtN(ss, 0) && ss.len() == 0
{
}

pub proof fn stepBaseOne()
    ensures exists |ss: Set<Seq<Steps>>| allEndAtN(ss, 1) && ss.len() == 1
{
}

pub proof fn stepBaseTwo()
    ensures exists |ss: Set<Seq<Steps>>| allEndAtN(ss, 2) && ss.len() == 2
{
}

pub spec fn plusOne(x: Seq<Steps>) -> Seq<Steps> {
    seq![Steps::One].add(x)
}

pub spec fn addOne(ss: Set<Seq<Steps>>) -> Set<Seq<Steps>>
    ensures forall |x| ss.contains(x) ==> addOne(ss).contains(plusOne(x)),
    ensures addOne(ss) == Set::new(|x| ss.contains(x) && plusOne(x) == x)
{
    Set::new(|x| exists |y| ss.contains(y) && x == plusOne(y))
}

pub proof fn UnequalSeqs<T>(xs: Seq<T>, ys: Seq<T>, someT: T)
    requires xs != ys
    ensures seq![someT].add(xs) != seq![someT].add(ys)
{
}

pub proof fn plusOneNotIn(ss: Set<Seq<Steps>>, x: Seq<Steps>)
    requires !ss.contains(x)
    ensures !addOne(ss).contains(plusOne(x))
{
}

pub proof fn addOneSize(ss: Set<Seq<Steps>>)
    ensures addOne(ss).len() == ss.len()
{
}

pub spec fn plusTwo(x: Seq<Steps>) -> Seq<Steps> {
    seq![Steps::Two].add(x)
}

pub spec fn addTwo(ss: Set<Seq<Steps>>) -> Set<Seq<Steps>>
    ensures forall |x| ss.contains(x) ==> addTwo(ss).contains(plusTwo(x)),
    ensures addTwo(ss) == Set::new(|x| exists |y| ss.contains(y) && x == plusTwo(y))
{
    Set::new(|x| exists |y| ss.contains(y) && x == plusTwo(y))
}

pub proof fn plusTwoNotIn(ss: Set<Seq<Steps>>, x: Seq<Steps>)
    requires !ss.contains(x)
    ensures !addTwo(ss).contains(plusTwo(x))
{
}

pub proof fn addTwoSize(ss: Set<Seq<Steps>>)
    ensures addTwo(ss).len() == ss.len()
{
}

pub proof fn stepSetsAdd(i: nat, steps: &[nat])
    requires i >= 2,
    requires steps.len() >= i + 1,
    requires forall |k: nat| k < i ==> exists |ss: Set<Seq<Steps>>| steps[k] == ss.len() && allEndAtN(ss, k)
    ensures exists |sp: Set<Seq<Steps>>| sp.len() == steps[i-1] + steps[i-2] && allEndAtN(sp, i)
{
}

pub fn climbStairs(n: nat) -> (count: nat)
    ensures exists |ss: Set<Seq<Steps>>| count == ss.len() && allEndAtN(ss, n)
{
}