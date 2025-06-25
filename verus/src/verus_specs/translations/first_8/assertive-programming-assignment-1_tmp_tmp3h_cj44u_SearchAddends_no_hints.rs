pub fn Main() {
    
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

spec fn HasAddends(q: Seq<int>, x: int) -> bool {
    exists|i: int, j: int| 0 <= i < j < q.len() && q[i] + q[j] == x
}

pub fn FindAddends(q: Seq<int>, x: int) -> (i: nat, j: nat)
    requires(Sorted(q) && HasAddends(q, x))
    ensures(i < j < q.len() && q[i as int] + q[j as int] == x)
{
    
}

spec fn IsValidIndex<T>(q: Seq<T>, i: nat) -> bool {
    0 <= i < q.len()
}

spec fn AreOreredIndices<T>(q: Seq<T>, i: nat, j: nat) -> bool {
    0 <= i < j < q.len()
}

spec fn AreAddendsIndices(q: Seq<int>, x: int, i: nat, j: nat) -> bool
    requires(IsValidIndex(q, i) && IsValidIndex(q, j))
{
    q[i as int] + q[j as int] == x
}

spec fn HasAddendsInIndicesRange(q: Seq<int>, x: int, i: nat, j: nat) -> bool
    requires(AreOreredIndices(q, i, j))
{
    HasAddends(q.subrange(i as int, (j + 1) as int), x)
}

spec fn LoopInv(q: Seq<int>, x: int, i: nat, j: nat, sum: int) -> bool {
    AreOreredIndices(q, i, j) &&
    HasAddendsInIndicesRange(q, x, i, j) &&
    AreAddendsIndices(q, sum, i, j)
}

proof fn LoopInvWhenSumIsBigger(q: Seq<int>, x: int, i: nat, j: nat, sum: int)
    requires(HasAddends(q, x))
    requires(Sorted(q))
    requires(sum > x)
    requires(LoopInv(q, x, i, j, sum))
    ensures(HasAddendsInIndicesRange(q, x, i, j - 1))
{
    
}