// <vc-preamble>
function min(a: seq<int>): int
    requires |a| > 0
    ensures min(a) in a
    ensures forall i :: 0 <= i < |a| ==> min(a) <= a[i]
{
    if |a| == 1 then a[0]
    else if a[0] <= min(a[1..]) then a[0]
    else min(a[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed reads clause as it's not needed for a pure predicate and was causing a compilation error. */
predicate IsDivisor(d: int, a: seq<int>)
    requires d > 0
    requires |a| > 0
{
    forall i :: 0 <= i < |a| ==> a[i] % d == 0
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires |a| > 0
    requires forall i :: 0 <= i < |a| ==> a[i] > 0
    ensures result == -1 || result in a
    ensures result != -1 ==> forall i :: 0 <= i < |a| ==> a[i] % result == 0
    ensures result == -1 ==> forall x :: x in a ==> exists i :: 0 <= i < |a| && a[i] % x != 0
    ensures (forall i :: 0 <= i < |a| ==> a[i] % (min(a)) == 0) ==> result == min(a)
    ensures (exists i :: 0 <= i < |a| && a[i] % (min(a)) != 0) ==> result == -1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): No changes as the previous fix was for a compilation error in the helper */
{
    var m := min(a);
    if IsDivisor(m, a)
    {
        result := m;
    } else {
        result := -1;
    }
}
// </vc-code>
