use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

spec fn is_first_even(even_index: int, lst: Seq<int>) -> bool
    recommends 0 <= even_index < lst.len() && is_even(lst[even_index])
{
    forall|i: int| 0 <= i < even_index ==> is_odd(lst[i])
}

spec fn is_first_odd(odd_index: int, lst: Seq<int>) -> bool
    recommends 0 <= odd_index < lst.len() && is_odd(lst[odd_index])
{
    forall|i: int| 0 <= i < odd_index ==> is_even(lst[i])
}


fn first_even_odd_indices(lst: Seq<int>) -> (r: (usize, usize))
    requires lst.len() >= 2,
    requires exists|i: int| 0 <= i < lst.len() && is_even(lst[i]),
    requires exists|i: int| 0 <= i < lst.len() && is_odd(lst[i]),
    ensures ({
        let (even_index, odd_index) = r;
        &&& 0 <= even_index < lst.len()
        &&& 0 <= odd_index < lst.len()
        &&& is_even(lst[even_index as int]) && is_first_even(even_index as int, lst)
        &&& is_odd(lst[odd_index as int]) && is_first_odd(odd_index as int, lst)
    }),
{
  assume(false);
  (0, 0)
}

// <vc-helpers>
// Updated helpers to support proofs in CODE
proof fn lemma_len_cast_nonneg<T>(s: Seq<T>) {
    // Seq length is non-negative; trivial lemma placeholder if needed.
    assert(s.len() as int >= 0);
}
// </vc-helpers>

// <vc-spec>
fn product_even_odd(lst: Seq<int>) -> (product: i32)
    requires lst.len() >= 2,
    requires exists|i: int| 0 <= i < lst.len() && is_even(lst[i]),
    requires exists|i: int| 0 <= i < lst.len() && is_odd(lst[i]),
    ensures exists|i: int, j: int| 0 <= i < lst.len() && is_even(lst[i]) && is_first_even(i, lst) && 
                                   0 <= j < lst.len() && is_odd(lst[j])  && is_first_odd(j, lst) && product as int == lst[i] * lst[j],
// </vc-spec>
// <vc-code>
{
    let n: int = lst.len() as int;

    // find first even index i
    let mut i: int = 0;
    while i < n && !is_even(lst@[i]) {
        invariant 0 <= i && i <= n;
        invariant forall|k: int| 0 <= k && k < i ==> is_odd(lst@[k]);
        decreases n - i;
        i = i + 1;
    }
    // prove that i < n (there is an even by precondition)
    proof {
        let k = choose(|k: int| 0 <= k && k < lst.len() as int && is_even(lst@[k]));
        if k < i {
            assert(forall|t: int| 0 <= t && t < i ==> is_odd(lst@[t]));
            assert(is_odd(lst@[k]));
            assert(is_even(lst@[k]));
            assert(false);
        } else {
            // k >= i, and k < n, so i < n
            assert(i <= k);
            assert(k < n);
            assert(i < n);
        }
    }
    assert(i < n);
    assert(is_even(lst@[i]));
    assert(forall|t: int| 0 <= t && t < i ==> is_odd(lst@[t]));
    let even_index: int = i;

    // find first odd index j
    let mut j: int = 0;
    while j < n && !is_odd(lst@[j]) {
        invariant 0 <= j && j <= n;
        invariant forall|k: int| 0 <= k && k < j ==> is_even(lst@[k]);
        decreases n - j;
        j = j + 1;
    }
    // prove that j < n (there is an odd by precondition)
    proof {
        let k = choose(|k: int| 0 <= k && k < lst.len() as int && is_odd(lst@[k]));
        if k < j {
            assert(forall|t: int| 0 <= t && t < j ==> is_even(lst@[t]));
            assert(is_even(lst@[k]));
            assert(is_odd(lst@[k]));
            assert(false);
        } else {
            // k >= j, and k < n, so j < n
            assert(j <= k);
            assert(k < n);
            assert(j < n);
        }
    }
    assert(j < n);
    assert(is_odd(lst@[j]));
    assert(forall|t: int| 0 <= t && t < j ==> is_even(lst@[t]));
    let odd_index: int = j;

    // compute product and return, and prove the existential postcondition
    let prod_int: int = lst@[even_index] * lst@[odd_index];
    let res: i32 = prod_int as i32;

    proof {
        // establish all required properties for the witnesses even_index and odd_index
        assert(0 <= even_index && even_index < lst.len() as int);
        assert(is_even(lst@[even_index]));
        assert(is_first_even(even_index, lst));
        assert(0 <= odd_index && odd_index < lst.len() as int);
        assert(is_odd(lst@[odd_index]));
        assert(is_first_odd(odd_index, lst));
        assert(res as int == lst@[even_index] * lst@[odd_index]);

        // produce the existential witness using these indices
        assert(exists|i: int, j: int|
            i == even_index && j == odd_index &&
            0 <= i && i < lst.len() as int && is_even(lst@[i]) && is_first_even(i, lst) &&
            0 <= j && j < lst.len() as int && is_odd(lst@[j]) && is_first_odd(j, lst) &&
            res as int == lst@[i] * lst@[j]
        );
    }

    res
}
// </vc-code>

fn main() {
}

}