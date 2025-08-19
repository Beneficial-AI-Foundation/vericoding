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


//IMPL 

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]

/* code modified by LLM (iteration 1): Added helper lemma to prove prefix sum property */
lemma prefix_sum_property(a: array<int>, c: array<int>, i: int, j: int)
 requires 0 <= i <= j <= a.Length
 requires is_prefix_sum_for(a, c)
 ensures sum(a, i, j) == c[j] - c[i]
{
 if i == j {
  // Base case: sum(a, i, i) == 0 and c[i] - c[i] == 0
 } else {
  // Inductive case
  prefix_sum_property(a, c, i, j-1);
  // sum(a, i, j) == a[j-1] + sum(a, i, j-1)
  // sum(a, i, j-1) == c[j-1] - c[i] (by inductive hypothesis)
  // c[j] == sum(a, 0, j) == sum(a, 0, j-1) + a[j-1] == c[j-1] + a[j-1]
  // Therefore: sum(a, i, j) == a[j-1] + (c[j-1] - c[i]) == (c[j-1] + a[j-1]) - c[i] == c[j] - c[i]
 }
}

method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
 requires 0 <= i <= j <= a.Length
 requires is_prefix_sum_for(a,c)
 ensures r == sum(a, i, j)
{
    /* code modified by LLM (iteration 1): Added lemma call to establish correctness */
    prefix_sum_property(a, c, i, j);
    r := c[j] - c[i];
}