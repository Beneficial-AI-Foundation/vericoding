Given n notes where each note i has maximum playable volume a_i and required total volume b_i,
find piano volume x_i and guitar volume y_i such that 1 ≤ x_i ≤ a_i, 1 ≤ y_i ≤ a_i, and x_i + y_i = b_i.
For playable notes, add x_i × y_i to total joy. For unplayable notes, subtract 1.
Return the maximum possible total joy.

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

lemma sum_contributions_lemma(a: seq<int>, b: seq<int>, i: int)
    requires |a| == |b|
    requires 0 <= i < |a|
    ensures sum_contributions(a[..i+1], b[..i+1]) == 
            sum_contributions(a[..i], b[..i]) + 
            (if b[i] > 1 && 2 * a[i] >= b[i] then
                var x := b[i] / 2;
                var y := b[i] - x;
                x * y
             else -1)
{
    if i == 0 {
        assert a[..1] == [a[0]];
        assert b[..1] == [b[0]];
        assert a[..0] == [];
        assert b[..0] == [];
    } else {
        sum_contributions_lemma(a[1..], b[1..], i-1);
        assert a[..i+1] == [a[0]] + a[1..][..i];
        assert b[..i+1] == [b[0]] + b[1..][..i];
        assert a[..i] == [a[0]] + a[1..][..i-1];
        assert b[..i] == [b[0]] + b[1..][..i-1];
    }
}

method solve(a: seq<int>, b: seq<int>) returns (result: int)
    requires |a| == |b|
    ensures result == sum_contributions(a, b)
{
    var total := 0;
    var i := 0;

    while i < |a|
        invariant 0 <= i <= |a|
        invariant total == sum_contributions(a[..i], b[..i])
    {
        var max_vol := a[i];
        var req_vol := b[i];
        var contribution: int;

        if req_vol > 1 && 2 * max_vol >= req_vol {
            // Can play this note - maximize x * y where x + y = req_vol
            var x := req_vol / 2;  // floor division
            var y := req_vol - x;  // this gives us ceiling
            contribution := x * y;
        } else {
            // Cannot play this note
            contribution := -1;
        }

        // Help Dafny see that the contribution matches the function definition
        assert contribution == (if req_vol > 1 && 2 * max_vol >= req_vol then
            var x := req_vol / 2;
            var y := req_vol - x;
            x * y
         else -1);

        // Prove the recursive relationship
        sum_contributions_lemma(a, b, i);

        total := total + contribution;
        i := i + 1;
    }

    // Help Dafny see that slicing the full sequence gives the original sequence
    assert a[..|a|] == a;
    assert b[..|b|] == b;
    assert total == sum_contributions(a[..|a|], b[..|b|]);

    result := total;
}
