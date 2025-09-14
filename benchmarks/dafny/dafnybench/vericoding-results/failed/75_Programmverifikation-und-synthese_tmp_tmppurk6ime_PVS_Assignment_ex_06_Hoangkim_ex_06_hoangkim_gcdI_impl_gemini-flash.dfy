//Problem01
//a)
ghost function gcd(x: int, y: int): int
    requires x > 0 && y > 0
{
    if x == y then x
    else if x > y then gcd(x - y, y)
    else gcd(x, y - x)
}

//b)
ghost function gcd'(x: int, y: int): int
    requires x > 0 && y > 0
    decreases if x > y then x else y
{
    if x == y then x
    else if x > y then gcd'(x - y, y)
    else gcd(y, x)
}

// <vc-helpers>
function gcd_func(x: int, y: int): int
    requires x > 0 && y > 0
{
    if x == y then x
    else if x > y then gcd_func(x - y, y)
    else gcd_func(x, y - x)
}
// Proof to show gcd_func is equivalent to gcd
lemma gcd_func_is_gcd(x: int, y: int) returns (res: int)
    requires x > 0 && y > 0
    ensures gcd_func(x, y) == gcd(x, y) && res == gcd_func(x,y) // Change ensurs to match the return (res)
    decreases x + y
{
    if x == y {
        res := x;
    } else if x > y {
        res := gcd_func_is_gcd(x - y, y); // Store and return the result of the recursive call
    } else { // x < y
        res := gcd_func_is_gcd(x, y - x); // Store and return the result of the recursive call
    }
}
// </vc-helpers>

// <vc-spec>
method gcdI(m: int, n: int) returns (d: int)
requires  m > 0 && n > 0 
ensures d == gcd(m, n);
// </vc-spec>
// <vc-code>
{
    var x := m;
    var y := n;
    // We don't need to call gcd_func_is_gcd(m, n) here. The loop invariants will handle the connection.
    while x != y
        invariant x > 0 && y > 0
        invariant gcd_func(x, y) == gcd_func(m, n)
        // We know that before the loop, x=m and y=n. So gcd_func(x,y) == gcd_func(m,n) is true.
        // We also know from the post-condition of gcd_func_is_gcd that gcd_func(a,b) == gcd(a,b)
        // So, we need to prove that gcd(x,y) == gcd(m,n) holds invariant.
        invariant gcd(x, y) == gcd(m, n) // Add the invariant for gcd to make the proof chain explicit
        decreases x + y
    {
        if x > y {
            x := x - y;
            // After x := x - y, we need to show gcd(x_new, y) == gcd(x_old, y) which simplifies to gcd(x-y, y) == gcd(x, y)
            // This is a property of GCD often used in Euclidean algorithm. Just showing the gcd_func equality is not sufficient for the final postcondition.
            // The lemma gcd_func_is_gcd does the job of bridging gcd_func and gcd. So we need to call it with the current (x, y) inside the loop.
            var _ := gcd_func_is_gcd(x, y); // This helps link gcd_func to gcd for the current x and y.
        } else {
            y := y - x;
            // Similar for y := y - x, we need to show gcd(x, y_new) == gcd(x, y_old) which simplifies to gcd(x, y-x) == gcd(x, y)
            var _ := gcd_func_is_gcd(x, y); // This helps link gcd_func to gcd for the current x and y.
        }
    }
    d := x;
    // At this point, x == y.
    // From invariant: gcd(x, y) == gcd(m, n).
    // Since x == y, we know that gcd(x, y) == x. (Or gcd(x,x) == x)
    // Therefore, x == gcd(m, n).
    // Since d == x, it follows that d == gcd(m, n), which satisfies the postcondition.
    // The invariant gcd(x,y) == gcd(m,n) is crucial here. Let's trace it.
    // Initial: gcd(m,n) == gcd(m,n) (true).
    // If x > y: gcd(x-y, y) == gcd(x,y). This is a property of gcd.
    // If x < y: gcd(x, y-x) == gcd(x,y). This is a property of gcd.
    // The proof that gcd(x,y) == gcd(m,n) holds through the loop iterations is implicitly handled by the standard properties of the Euclidean algorithm,
    // but stating it as an invariant helps Dafny verify it. The gcd_func_is_gcd lemma helps relate our custom gcd_func to the primitive gcd.
}
// </vc-code>

