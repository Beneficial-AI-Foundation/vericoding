spec fn knows(a: int, b: int) -> bool;

spec fn isCelebrity(n: int, i: int) -> bool
    requires n >= 0 && 0 <= i < n
{
    forall|j: int| 0 <= j < n && i != j ==> knows(j, i) && !knows(i, j)
}

proof fn knowerCannotBeCelebrity(n: int, i: int)
    requires n >= 0 && 0 <= i < n
    ensures (exists|j: int| 0 <= j < n && j != i && knows(i, j)) ==> !isCelebrity(n, i)
{
}

pub fn isCelebrityP(n: int, i: int) -> (r: bool)
    requires(n >= 0 && 0 <= i < n)
    ensures(r <==> isCelebrity(n, i))
{
}

pub fn findCelebrity(n: int) -> (r: int)
    requires(2 <= n <= 100)
    ensures(0 <= r < n ==> isCelebrity(n, r))
    ensures(r == -1 ==> forall|i: int| 0 <= i < n ==> !isCelebrity(n, i))
{
}