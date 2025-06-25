//ATOM
// Empty atom block - no content needed

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

//IMPL queryFast

/* code modified by LLM (iteration 1): Added lemma to prove the mathematical relationship between prefix sums and range sums */
lemma sum_prefix_property(a: array<int>, c: array<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a, c)
    ensures sum(a, i, j) == c[j] - c[i]
{
    if i == j {
        // Base case: empty range
        assert sum(a, i, j) == 0;
        assert c[j] == sum(a, 0, j);
        assert c[i] == sum(a, 0, i);
        assert c[j] == c[i];
    } else {
        // Inductive case
        sum_decomposition_lemma(a, i, j);
        sum_prefix_property(a, c, i, j-1);
    }
}

/* code modified by LLM (iteration 1): Added helper lemma to decompose sum into parts */
lemma sum_decomposition_lemma(a: array<int>, i: int, j: int)
    requires 0 <= i < j <= a.Length
    ensures sum(a, i, j) == sum(a, i, j-1) + a[j-1]
{
    // This follows directly from the definition of sum
}

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
 requires 0 <= i <= j <= a.Length
 requires is_prefix_sum_for(a,c)
 ensures r == sum(a, i, j)
{
    /* code modified by LLM (iteration 1): Added lemma call to establish the correctness of the computation */
    sum_prefix_property(a, c, i, j);
    r := c[j] - c[i];
}