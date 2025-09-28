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
lemma TriangleStep(k: nat)
  ensures triangle(k + 1) == triangle(k) + k + 1
{}
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
    var i := idx;
    var s := sum;
    while i < n
        invariant i <= n
        invariant s == triangle(i)
        decreases n - i
    {
        i := i + 1;
        s := s + i;
    }
    new_sum := s;
}
// </vc-code>
