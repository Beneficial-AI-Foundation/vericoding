function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}
// pure-end
method is_multiply_prime(x: nat) returns (ans : bool)
    // pre-conditions-start
    requires x > 1
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    // post-conditions-end
{
    // impl-start
    for a := 2 to x
        // invariants-start
        invariant forall i: nat, j: nat, k: nat :: (Prime(i) && Prime(j) && Prime(k) && i < a) ==> x != i * j * k
        // invariants-end
    {
        if Prime(a) {
            for b := 2 to x
                // invariants-start
                invariant forall j: nat, k: nat :: (Prime(j) && Prime(k) && j < b) ==> x != a * j * k
                // invariants-end
            {
                if Prime(b) {
                    for c := 2 to x
                        // invariants-start
                        invariant forall k: nat :: (Prime(k) && k < c) ==> x != a * b * k
                        // invariants-end
                    {
                        if Prime(c) && x == a * b * c {
                            return true;
                        }
                    }
                }
            }
        }
    }
    return false;
    // impl-end
}
