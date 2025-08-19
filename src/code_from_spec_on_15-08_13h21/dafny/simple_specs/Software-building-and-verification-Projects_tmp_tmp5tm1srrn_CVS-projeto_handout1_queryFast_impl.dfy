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

/* code modified by LLM (iteration 1): Added helper lemma to prove sum decomposition property */
lemma sum_decomposition(a: array<int>, i: int, j: int)
 requires 0 <= i <= j <= a.Length
 ensures sum(a, 0, j) - sum(a, 0, i) == sum(a, i, j)
{
 if i == j {
  // Base case: sum(a, i, i) == 0
  // sum(a, 0, i) - sum(a, 0, i) == 0
 } else {
  // Inductive case: use the fact that sum(a, i, j) == a[j-1] + sum(a, i, j-1)
  sum_decomposition(a, i, j-1);
  // Now we know: sum(a, 0, j-1) - sum(a, 0, i) == sum(a, i, j-1)
  // And sum(a, 0, j) == sum(a, 0, j-1) + a[j-1] (by definition)
  // So sum(a, 0, j) - sum(a, 0, i) == sum(a, 0, j-1) + a[j-1] - sum(a, 0, i)
  //                                 == (sum(a, 0, j-1) - sum(a, 0, i)) + a[j-1]
  //                                 == sum(a, i, j-1) + a[j-1]
  //                                 == sum(a, i, j)
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
    /* code modified by LLM (iteration 1): Added lemma call to establish the relationship between prefix sums and range sum */
    sum_decomposition(a, i, j);
    r := c[j] - c[i];
}