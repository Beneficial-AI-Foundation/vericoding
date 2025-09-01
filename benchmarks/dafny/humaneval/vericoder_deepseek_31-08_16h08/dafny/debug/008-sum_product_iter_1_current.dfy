function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

// <vc-helpers>
lemma sum_concat(a: seq<int>, b: seq<int>)
    ensures sum(a + b) == sum(a) + sum(b)
    decreases |a|
{
    if |a| == 0 {
        assert a + b == b;
    } else {
        var a' := a[1..];
        calc {
            sum(a + b);
            a[0] + sum((a + b)[1..]);
            a[0] + sum(a' + b);
            a[0] + (sum(a') + sum(b));
            (a[0] + sum(a')) + sum(b);
            sum(a) + sum(b);
        }
    }
}

lemma prod_concat(a: seq<int>, b: seq<int>)
    ensures prod(a + b) == prod(a) * prod(b)
    decreases |a|
{
    if |a| == 0 {
        assert a + b == b;
    } else {
        var a' := a[1..];
        calc {
            prod(a + b);
            a[0] * prod((a + b)[1..]);
            a[0] * prod(a' + b);
            a[0] * (prod(a') * prod(b));
            (a[0] * prod(a')) * prod(b);
            prod(a) * prod(b);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (s : int, p : int)
    // post-condition-start
    ensures s == sum(numbers)
    ensures p == prod(numbers)
    // post-condition-end
// </vc-spec>
// <vc-code>
{
    if |numbers| == 0 {
        s := 0;
        p := 1;
    } else {
        var head := numbers[0];
        var tail := numbers[1..];
        var s_tail, p_tail := sum_product(tail);
        s := head + s_tail;
        p := head * p_tail;
    }
}
// </vc-code>

