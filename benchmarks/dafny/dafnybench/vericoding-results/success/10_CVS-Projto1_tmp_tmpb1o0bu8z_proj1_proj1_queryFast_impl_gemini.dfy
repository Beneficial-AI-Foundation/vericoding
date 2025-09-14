// <vc-preamble>
function sum (a:array<int>, i:int, j:int) :int
decreases j
reads a
requires 0 <= i <= j <= a.Length
{
    if i == j then
        0
    else
        a[j-1] + sum(a, i, j-1)
}

predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{
    a.Length + 1 == c.Length
    && c[0] == 0
    && forall j :: 1 <= j <= a.Length ==> c[j] == sum(a,0,j)
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
requires a.Length > 0
ensures forall j::0 <= j < a.Length ==> mem(a[j],l)
{
  assume{:axiom} false;
}

function mem<T(==)> (x: T, l:List<T>) : bool
decreases l
{
    match l
    case Nil => false
    case Cons(y,r)=> if (x==y) then true else mem(x,r)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed invalid `reads` clause from lemma definition. */
lemma SumAdditive(a: array<int>, k: int, m: int, n: int)
    requires 0 <= k <= m <= n <= a.Length
    ensures sum(a, k, n) == sum(a, k, m) + sum(a, m, n)
    decreases n - m
{
    if m < n {
        SumAdditive(a, k, m, n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i,j)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Used the SumAdditive lemma to relate the prefix sum array to the desired range sum. */
  SumAdditive(a, 0, i, j);
  r := c[j] - c[i];
}
// </vc-code>
