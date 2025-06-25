// SPEC 
pub fn Main()
{
}


// ATOM 

spec fn Sorted(q: Seq<int>) -> bool
{
	forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j] 
}


// ATOM 

spec fn HasAddends(q: Seq<int>, x: int) -> bool
{
	exists|i: int, j: int| 0 <= i < j < q.len() && q[i] + q[j] == x
}


// SPEC 

pub fn FindAddends(q: Seq<int>, x: int) -> (i: nat, j: nat)
	requires(Sorted(q) && HasAddends(q, x))
	ensures(|result: (nat, nat)| result.0 < result.1 < q.len() && q[result.0] + q[result.1] == x)
{
}


// ATOM 

spec fn IsValidIndex<T>(q: Seq<T>, i: nat) -> bool
{
	0 <= i < q.len()
}


// ATOM 

spec fn AreOreredIndices<T>(q: Seq<T>, i: nat, j: nat) -> bool
{
	0 <= i < j < q.len()
}


// ATOM 

spec fn AreAddendsIndices(q: Seq<int>, x: int, i: nat, j: nat) -> bool
	recommends(IsValidIndex(q, i) && IsValidIndex(q, j))
{
	q[i] + q[j] == x
}


// ATOM 

spec fn HasAddendsInIndicesRange(q: Seq<int>, x: int, i: nat, j: nat) -> bool
	recommends(AreOreredIndices(q, i, j))
{
	HasAddends(q.subrange(i, j + 1), x)
}


// ATOM 

spec fn LoopInv(q: Seq<int>, x: int, i: nat, j: nat, sum: int) -> bool
{
	AreOreredIndices(q, i, j) &&
	HasAddendsInIndicesRange(q, x, i, j) &&
	AreAddendsIndices(q, sum, i, j)
}


// ATOM 

proof fn LoopInvWhenSumIsBigger(q: Seq<int>, x: int, i: nat, j: nat, sum: int)
	requires(HasAddends(q, x))
	requires(Sorted(q))
	requires(sum > x)
	requires(LoopInv(q, x, i, j, sum))
	ensures(HasAddendsInIndicesRange(q, x, i, j - 1))
{
}