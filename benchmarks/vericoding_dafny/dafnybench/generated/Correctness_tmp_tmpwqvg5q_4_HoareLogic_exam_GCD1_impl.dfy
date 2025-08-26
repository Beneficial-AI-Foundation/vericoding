// Redo for exam

// <vc-spec>
function gcd(a: nat, b: nat): nat
    decreases b
{
    if b == 0 then a
    else gcd(b, a % b)
}

lemma r1(a: nat)
    ensures gcd(a, 0) == a
{
    // follows directly from definition
}

lemma r2(a:nat)
    ensures gcd(a, a) == a
{
    if a == 0 {
        // gcd(0, 0) = 0 by definition
    } else {
        // gcd(a, a) = gcd(a, a % a) = gcd(a, 0) = a
        assert a % a == 0;
        r1(a);
    }
}

lemma r3(a: nat, b: nat)
    ensures gcd(a, b) == gcd(b, a)
{
    if b == 0 {
        r1(a);
        if a == 0 {
            r1(b);
        } else {
            gcd_comm_helper(b, a);
        }
    } else if a == 0 {
        r1(b);
        gcd_comm_helper(a, b);
    } else {
        gcd_comm_helper(a, b);
    }
}

lemma r4 (a: nat, b: nat)
    ensures b > 0 ==> gcd(a, b) == gcd(b, a % b)
{
    // follows directly from definition when b > 0
}

// <vc-helpers>
lemma gcd_comm_helper(a: nat, b: nat)
    ensures gcd(a, b) == gcd(b, a)
    decreases a + b
{
    if b == 0 {
        r1(a);
        if a == 0 {
            r1(b);
        }
    } else if a == 0 {
        r1(b);
    } else {
        // Both a > 0 and b > 0
        if a < b {
            // When a < b, we have a % b = a
            assert a % b == a;
            // gcd(a, b) = gcd(b, a % b) = gcd(b, a)
            // We can use the fact that gcd(b, a) = gcd(a, b % a)
            // and b % a < b, so (b % a) + a < a + b
            calc {
                gcd(a, b);
                gcd(b, a % b);
                gcd(b, a);
            }
            // Use transitivity with a recursive call on smaller values
            calc {
                gcd(b, a);
                gcd(a, b % a);
                { gcd_comm_helper(a, b % a); }
                gcd(b % a, a);
                gcd(a, (b % a) % a);
                { assert b < a + b && a > 0 ==> b % a < a; }
                gcd(a, b % a);
            }
        } else {
            // When a >= b > 0, we have a % b < a, so b + (a % b) < a + b
            calc {
                gcd(a, b);
                gcd(b, a % b);
                { gcd_comm_helper(b, a % b); }
                gcd(a % b, b);
                gcd(b, (a % b) % b);
                { assert (a % b) % b == a % b; }
                gcd(b, a % b);
            }
        }
    }
}
// </vc-helpers>

method GCD1(a: int, b: int) returns (r: int)
    requires a > 0 && b > 0
    ensures gcd(a,b) == r
    decreases b
// </vc-spec>
// <vc-code>
{
    if b == 1 {
        r := 1;
        assert gcd(a, 1) == 1;
    } else {
        var remainder := a % b;
        if remainder == 0 {
            r := b;
            r1(b);
        } else {
            var temp := GCD1(b, remainder);
            r := temp;
            r4(a, b);
        }
    }
}
// </vc-code>