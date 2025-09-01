```vc-helpers
proof fn prime_of_divides_no_smaller(k: nat, j: nat)
    requires
        2 <= j,
        k % j == 0,
        forall|d: nat| 2 <= d < j ==> k % d != 0,
    ensures
        is_prime(j),
{
    // Show forall t. 1 < t < j ==> j % t != 0
    assert(forall|t: nat| 1 < t < j ==> j % t != 0);
    proof {
        ::proof_by_contradiction:
        assume(exists|t: nat| 1 < t < j && j % t == 0);
        // Extract such a t
        choose |t: nat| (1 < t && t < j && j % t == 0);
        // From j % t == 0 and k % j == 0 we get k % t == 0, contradicting the forall assumption
        assert(j % t == 0);
        // j = t * (j / t)
        let q = j / t;
        assert(j == t * q);
        // k = j * (k / j)
        let m = k / j;
        assert(k == j * m);
        // hence k = t * (q * m)
        calc::calc! {
            k;
            equals j * m;
            equals t * (q * m);
        }
