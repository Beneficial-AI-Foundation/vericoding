function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)
    // pre-conditions-start
    requires x > 1
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    // post-conditions-end
// </vc-spec>
// <vc-code>
for a := 2 to x/4 + 1 {
        if Prime(a) && x % a == 0 {
            var rem1 := x / a;
            for b := 2 to rem1/2 + 1 {
                if Prime(b) && rem1 % b == 0 {
                    var c := rem1 / b;
                    if Prime(c) {
                        return true;
                    }
                }
            }
        }
    }
    return false;
// </vc-code>

