function sum_contributions(a: seq<int>, b: seq<int>): int
    requires |a| == |b|
{
    if |a| == 0 then 0
    else 
        (if b[0] > 1 && 2 * a[0] >= b[0] then
            var x := b[0] / 2;
            var y := b[0] - x;
            x * y
         else -1) + sum_contributions(a[1..], b[1..])
}

// <vc-helpers>
lemma sum_contributions_extension(a: seq<int>, b: seq<int>, i: int)
    requires |a| == |b|
    requires 0 <= i < |a|
    ensures sum_contributions(a[0..i+1], b[0..i+1]) == 
            sum_contributions(a[0..i], b[0..i]) + 
            (if b[i] > 1 && 2 * a[i] >= b[i] then
                var x := b[i] / 2;
                var y := b[i] - x;
                x * y
             else -1)
{
    if i == 0 {
        assert a[0..1] == [a[0]];
        assert b[0..1] == [b[0]];
        assert a[0..0] == [];
        assert b[0..0] == [];
    } else {
        assert a[0..i+1] == [a[0]] + a[1..i+1];
        assert b[0..i+1] == [b[0]] + b[1..i+1];
        assert a[1..i+1] == a[1..][0..i];
        assert b[1..i+1] == b[1..][0..i];
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, b: seq<int>) returns (result: int)
    requires |a| == |b|
    ensures result == sum_contributions(a, b)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant result == sum_contributions(a[0..i], b[0..i])
    {
        var contribution := if b[i] > 1 && 2 * a[i] >= b[i] then
            var x := b[i] / 2;
            var y := b[i] - x;
            x * y
        else -1;
        
        sum_contributions_extension(a, b, i);
        result := result + contribution;
        i := i + 1;
    }
}
// </vc-code>

