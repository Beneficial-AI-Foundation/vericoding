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
lemma sum_contributions_append(a: seq<int>, b: seq<int>, i: int)
    requires |a| == |b|
    requires 0 <= i <= |a|
    ensures sum_contributions(a[i..], b[i..]) == 
            if i == |a| then 0
            else (if b[i] > 1 && 2 * a[i] >= b[i] then
                    var x := b[i] / 2;
                    var y := b[i] - x;
                    x * y
                  else -1) + sum_contributions(a[i+1..], b[i+1..])
{
    if i == |a| {
        assert a[i..] == [];
        assert b[i..] == [];
    } else {
        assert a[i..][0] == a[i];
        assert b[i..][0] == b[i];
        assert a[i..][1..] == a[i+1..];
        assert b[i..][1..] == b[i+1..];
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
    var i := |a|;
    
    while i > 0
        invariant 0 <= i <= |a|
        invariant result == sum_contributions(a[i..], b[i..])
    {
        i := i - 1;
        
        var contribution: int;
        if b[i] > 1 && 2 * a[i] >= b[i] {
            var x := b[i] / 2;
            var y := b[i] - x;
            contribution := x * y;
        } else {
            contribution := -1;
        }
        
        sum_contributions_append(a, b, i);
        result := contribution + result;
    }
}
// </vc-code>

