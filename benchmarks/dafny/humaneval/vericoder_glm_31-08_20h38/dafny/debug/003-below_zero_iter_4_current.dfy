function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

// <vc-helpers>
lemma psum_append(s: seq<int>, x: int)
    ensures psum(s + [x]) == psum(s) + x
{
    if |s| == 0 {
        calc {
            psum(s + [x]);
            psum([x]);
            { assert [x][0] == x; }
            psum([]) + [x][0];
            0 + x;
        }
    } else {
        calc {
            psum(s + [x]);
            psum((s + [x])[..|s + [x]| - 1]) + (s + [x])[|s + [x]| - 1];
            psum(s + [x][..|s|]) + (s + [x])[|s|];
            { assert s + [x][..|s|] == s; }
            psum(s) + (s + [x])[|s|];
            { assert (s + [x])[|s|] == x; }
            psum(s) + x;
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
{
    var cum := 0;
    var i := 0;
    while i < |ops|
        invariant 0 <= i <= |ops|
        invariant cum == psum(ops[..i])
        invariant forall k :: 0 <= k <= i ==> psum(ops[..k]) >= 0
    {
        cum := cum + ops[i];
        if cum < 0 {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>

