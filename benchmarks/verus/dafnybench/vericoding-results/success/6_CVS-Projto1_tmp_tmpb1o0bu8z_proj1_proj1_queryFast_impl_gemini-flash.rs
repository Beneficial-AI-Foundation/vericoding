use vstd::prelude::*;

verus! {

// Exercise 1.a)
spec fn sum(a: Seq<int>, i: int, j: int) -> int
    decreases j - i
{
    if i == j {
        0
    } else if i < j && j-1 < a.len() {
        a[j-1] + sum(a, i, j-1)
    } else {
        0  // default case
    }
}

// Exercise 1.b)

// Exercise 1.c)

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool {
    a.len() + 1 == c.len()
    && c[0] == 0
    && forall |j: int| #![auto] 1 <= j <= a.len() ==> c[j] == sum(a, 0, j)
}

// Exercise 2.
pub enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> }
}

fn from_array<T: Copy + PartialEq>(a: &Vec<T>) -> (l: List<T>)
    requires a.len() > 0
    ensures forall |j: int| #![auto] 0 <= j < a.len() ==> mem(a@[j], &l)
{
    assume(false);
    List::Nil
}

spec fn mem<T: PartialEq>(x: T, l: &List<T>) -> bool
    decreases l
{
    match l {
        List::Nil => false,
        List::Cons { head: y, tail: r } => if x == *y { true } else { mem(x, r) }
    }
}

// <vc-helpers>
#[verifier(nonlinear)] 
proof fn lemma_sum_relation(a: Seq<int>, c: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a, c),
    ensures
        sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i)
    decreases j - i
{
    if i == j {
        assert(sum(a, i, j) == 0);
        assert(c[j] == sum(a, 0, j)); // From is_prefix_sum_for
        assert(c[i] == sum(a, 0, i)); // From is_prefix_sum_for
        assert(sum(a, 0, j) - sum(a, 0, i) == c[j] - c[i]);
        assert(c[j] - c[i] == 0) by {
            assert(i == j);
        };
    } else {
        // Case 0 <= i < j <= a.len()
        assert(1 <= j); // Must be true when j > i >= 0
        if j > 0 { // This case covers j >= 1
            if i == 0 {
                // Base case for the recursive sum definition (sum(a,0,j)) and for the lemma.
                // We directly leverage the is_prefix_sum_for definition.
                assert(sum(a, 0, j) == c[j]);
                assert(sum(a, 0, i) == sum(a, 0, 0));
                assert(c[0] == 0);
                assert(sum(a, 0, 0) == 0);
                assert(sum(a, i, j) == sum(a, 0, j));
                assert(sum(a, 0, j) - sum(a, 0, i) == c[j] - c[0]);
                assert(sum(a, 0, j) == c[j]); // This should be provable now
            } else { // 0 < i < j
                // Inductive step: j-1
                lemma_sum_relation(a, c, i, j - 1);
                assert(sum(a, i, j) == a[j - 1] + sum(a, i, j - 1));
                assert(sum(a, i, j - 1) == sum(a, 0, j - 1) - sum(a, 0, i));
                
                // Relate sums to c array elements through is_prefix_sum_for definition
                assert(c[j] == sum(a, 0, j));
                assert(c[j-1] == sum(a, 0, j-1));
                assert(c[i] == sum(a, 0, i));
                
                // Show that c[j] == a[j-1] + c[j-1]
                assert(sum(a, 0, j) == a[j-1] + sum(a, 0, j-1)); // From sum definition
                assert(c[j] == a[j-1] + c[j-1]); // From is_prefix_sum_for (c[j] == sum(a,0,j))
                
                // Now combine the pieces
                assert(sum(a, i, j) == a[j-1] + (sum(a, 0, j-1) - sum(a, 0, i)));
                assert(sum(a, 0, j) - sum(a, 0, i) == (a[j-1] + sum(a, 0, j-1)) - sum(a, 0, i));
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
proof fn query_fast(a: Seq<int>, c: Seq<int>, i: int, j: int) -> (r: int)
    requires 
        is_prefix_sum_for(a, c) && 0 <= i <= j <= a.len() < c.len()
    ensures r == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
    // The sum(a,i,j) can be calculated as c[j] - c[i] if sum(a, 0, i) and sum(a, 0, j) are known
    // from the prefix sum array c.
    // Specifically, sum(a, 0, j) is c[j] and sum(a, 0, i) is c[i].
    // So sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i) == c[j] - c[i].
     
    // Proof for i == j:
    if i == j {
        assert(sum(a,i,j) == 0);
        assert(c[j] == sum(a,0,j)); // From is_prefix_sum_for
        assert(c[i] == sum(a,0,i)); // From is_prefix_sum_for
        assert(c[j] - c[i] == sum(a,0,j) - sum(a,0,i));
        assert(sum(a,0,j) - sum(a,0,i) == 0); // Since i == j
    } else if i == 0 {
        // If i == 0, then sum(a, 0, j) must be equal to c[j]
        // Since c[0] == 0, then sum(a, 0, j) == c[j] - c[0]
        assert(c[j] == sum(a, 0, j)); // From is_prefix_sum_for
        assert(c[0] == 0); // From is_prefix_sum_for
        assert(sum(a, 0, 0) == 0); // From sum definition
        assert(sum(a, 0, j) == c[j] - c[0]); // This is direct from is_prefix_sum_for
    } else {
        // For 0 < i < j, we need to prove sum(a,i,j) == sum(a,0,j) - sum(a,0,i)
        // This is a common property of prefix sums.
        // We can prove it by induction on j-i.
        lemma_sum_relation(a, c, i, j);
    }

    c[j] - c[i]
}
// </vc-code>

fn main() {}

}