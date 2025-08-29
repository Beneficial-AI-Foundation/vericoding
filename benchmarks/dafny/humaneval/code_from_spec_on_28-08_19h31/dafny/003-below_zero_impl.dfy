function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

// <vc-helpers>
function prefix_sum(s: seq<int>, n: int): int
    requires 0 <= n <= |s|
{
    if n == 0 then 0
    else prefix_sum(s, n-1) + s[n-1]
}

lemma prefix_sum_equivalence(s: seq<int>, n: int)
    requires 0 <= n <= |s|
    ensures prefix_sum(s, n) == psum(s[..n])
{
    if n == 0 {
        assert s[..0] == [];
        assert psum([]) == 0;
        assert prefix_sum(s, 0) == 0;
    } else {
        calc {
            prefix_sum(s, n);
            prefix_sum(s, n-1) + s[n-1];
            { prefix_sum_equivalence(s, n-1); }
            psum(s[..(n-1)]) + s[n-1];
            { assert s[..n] == s[..(n-1)] + [s[n-1]]; }
            psum(s[..n]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method below_zero(ops: seq<int>) returns (res : bool)
    // post-conditions-start
    ensures res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures !res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
method BelowZero(ops: seq<int>) returns (res: bool)
    ensures res ==> forall i: int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures !res ==> exists i: int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
{
    var current_sum := 0;
    var i := 0;
    while i < |ops|
        invariant 0 <= i <= |ops|
        invariant current_sum == psum(ops[..i])
        invariant forall k: int :: 0 <= k < i ==> psum(ops[..k]) >= 0
    {
        current_sum := current_sum + ops[i];
        assert ops[..i+1] == ops[..i] + [ops[i]];
        assert psum(ops[..i+1]) == psum(ops[..i]) + ops[i];
        assert psum(ops[..i+1]) == current_sum;
        if current_sum < 0 {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>
