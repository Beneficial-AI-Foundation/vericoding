use vstd::prelude::*;

verus! {

// 1 a)

// [ai, aj[
spec fn sum(a: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
    decreases j - i
    when 0 <= i <= j <= a.len()
{
    if i == j { 0 }
    else { a[j-1] + sum(a, i, j-1) }
}

// 1 b)

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool
{
    a.len() + 1 == c.len() && 
    forall|i: int| #![auto] 0 <= i <= a.len() ==> c[i] == sum(a, 0, i)
}

// <vc-helpers>
proof fn lemma_sum_range(a: Seq<int>, start: int, end: int, k: int)
    requires
        0 <= start <= end <= a.len(),
        start <= k <= end,
    ensures
        sum(a, start, end) == sum(a, start, k) + sum(a, k, end),
    decreases end - start
{
    if start == end {
        // Base case: range is empty, all sums are 0
        assert(sum(a, start, end) == 0);
        assert(sum(a, start, k) == 0); // Since start == k == end
        assert(sum(a, k, end) == 0);
    } else if k == start {
        // If k is the start, sum(a, start, k) is 0
        assert(sum(a, start, k) == 0);
        assert(sum(a, start, end) == sum(a, k, end));
    } else if k == end {
        // If k is the end, sum(a, k, end) is 0
        assert(sum(a, k, end) == 0);
        assert(sum(a, start, end) == sum(a, start, k));
    } else {
        // Recursive step: reduce the problem size
        // sum(a, start, end) == a[end-1] + sum(a, start, end-1)
        // sum(a, start, k)   == a[k-1]   + sum(a, start, k-1)
        // sum(a, k, end)     == a[end-1] + sum(a, k, end-1)

        // Inductively prove or use another lemma if needed to connect these.
        // For now, let's trace the induction with an example or direct use.
        // The property of sum being associative allows this split.
        // Sum definition: sum(a, i, j) = a[j-1] + sum(a, i, j-1)
        // So, sum(a, start, end)
        // = a[end-1] + sum(a, start, end-1)
        // And sum(a, start, k) + sum(a, k, end)
        // = sum(a, start, k) + (a[end-1] + sum(a, k, end-1))
        // So we need to show: sum(a, start, end-1) == sum(a, start, k) + sum(a, k, end-1)
        // This is exactly the recursive call:
        lemma_sum_range(a, start, end - 1, k);
    }
}
// </vc-helpers>

// <vc-spec>
proof fn queryFast(a: Seq<int>, c: Seq<int>, i: int, j: int) -> (r: int)
    requires 0 <= i <= j <= a.len(),
             is_prefix_sum_for(a, c)
    ensures r == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
    // r == sum(a, i, j)
    // We know c[k] == sum(a, 0, k) for all 0 <= k <= a.len()

    // We want to show sum(a, i, j) == c[j] - c[i]
    // From the definition of prefix sums:
    // c[j] = sum(a, 0, j)
    // c[i] = sum(a, 0, i)

    // Using lemma_sum_range: sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j)
    // Substituting c[j] and c[i]:
    // c[j] == c[i] + sum(a, i, j)
    // Therefore, sum(a, i, j) == c[j] - c[i]

    // The proof block is not needed here as it's a `proof fn`,
    // and assertions within it act as steps of the proof rather than
    // runtime assertions. The Verus verifier will automatically
    // connect the dots if the logic is sound and lemmas are provided.
    // The previous error was because `proof { ... }` blocks are for
    // `spec` methods, or methods with `decreases` clauses and no body.
    // This `queryFast` is a `proof fn` itself.

    // Directly assert the properties and use the lemma.
    // Verus will check these automatically using the `requires` clauses
    // and previously proven lemmas.
    // Assertions based on `is_prefix_sum_for` are implicitly guaranteed by the `requires` clause.
    // assert(c[j] == sum(a, 0, j)); // This is true by requires is_prefix_sum_for(a, c)
    // assert(c[i] == sum(a, 0, i)); // This is true by requires is_prefix_sum_for(a, c)

    lemma_sum_range(a, 0, j, i); // This proves sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j)

    // Now, combine the facts. Verus should be able to deduce:
    // c[j] == sum(a, 0, j) (from is_prefix_sum_for)
    // c[i] == sum(a, 0, i) (from is_prefix_sum_for)
    // sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j) (from lemma_sum_range)
    // Therefore, c[j] == c[i] + sum(a, i, j)
    // Which means sum(a, i, j) == c[j] - c[i]

    // No explicit `assert` statements are required inside a `proof fn`
    // when the logic directly follows from `requires` and `lemma` calls.
    // The `ensures` clause of the `proof fn` is what needs to be satisfied.
    c[j] - c[i]
}
// </vc-code>

fn main() {
}

}