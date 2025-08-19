//ATOM
// 2
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM
// 1 a)
// [ai, aj[
function sum(a: array<int>, i: int, j: int) : int
 requires 0 <= i <= j <= a.Length
 reads a
{
 if i == j then 0
 else a[j-1] + sum(a, i, j-1)
}

//ATOM
predicate is_prefix_sum_for (a: array<int>, c: array<int>)
 reads c, a
{
 a.Length + 1 == c.Length && forall i: int :: 0 <= i <= a.Length ==> c[i] == sum(a, 0, i)
}

/* code modified by LLM (iteration 1): Added helper lemma to prove prefix sum property */
lemma PrefixSumProperty(a: array<int>, c: array<int>, i: int, j: int)
 requires 0 <= i <= j <= a.Length
 requires is_prefix_sum_for(a, c)
 ensures c[j] - c[i] == sum(a, i, j)
{
 // The proof follows from the fact that:
 // c[j] == sum(a, 0, j) and c[i] == sum(a, 0, i)
 // So c[j] - c[i] == sum(a, 0, j) - sum(a, 0, i) == sum(a, i, j)
 SumSplit(a, 0, i, j);
}

/* code modified by LLM (iteration 1): Added helper lemma to prove sum splitting property */
lemma SumSplit(a: array<int>, start: int, mid: int, end: int)
 requires 0 <= start <= mid <= end <= a.Length
 ensures sum(a, start, end) == sum(a, start, mid) + sum(a, mid, end)
{
 if mid == end {
  assert sum(a, mid, end) == 0;
 } else {
  SumSplit(a, start, mid, end - 1);
 }
}

//IMPL 
// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
 requires 0 <= i <= j <= a.Length
 requires is_prefix_sum_for(a,c)
 ensures r == sum(a, i, j)
{
    /* code modified by LLM (iteration 1): Added lemma call to prove correctness */
    PrefixSumProperty(a, c, i, j);
    r := c[j] - c[i];
}