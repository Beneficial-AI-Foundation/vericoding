// <vc-preamble>
function triangle(n: nat): nat
    decreases n
{
    if n == 0 then
        0
    else
        n + triangle(n - 1)
}
// </vc-preamble>

// <vc-helpers>
lemma TriangleIncremental(idx: nat, sum: nat)
    requires sum == triangle(idx)
    ensures sum + (idx + 1) == triangle(idx + 1)
{
    if idx == 0 {
        assert triangle(1) == 1 + triangle(0) == 1 + 0 == 1;
        assert sum + (idx + 1) == 0 + 1 == 1;
    } else {
        assert triangle(idx + 1) == (idx + 1) + triangle(idx);
        assert sum + (idx + 1) == triangle(idx) + (idx + 1) == triangle(idx + 1);
    }
}
// </vc-helpers>

// <vc-spec>
method tail_triangle(n: nat, idx: nat, sum: nat) returns (new_sum: nat)
    requires idx <= n
    requires sum == triangle(idx)
    requires triangle(n) < 0x1_0000_0000
    ensures new_sum == triangle(n)
// </vc-spec>
// <vc-code>
{
    new_sum := sum;
    var current_idx := idx;
    
    while current_idx < n
        invariant current_idx <= n
        invariant new_sum == triangle(current_idx)
        decreases n - current_idx
    {
        TriangleIncremental(current_idx, new_sum);
        current_idx := current_idx + 1;
        new_sum := new_sum + current_idx;
    }
}
// </vc-code>
