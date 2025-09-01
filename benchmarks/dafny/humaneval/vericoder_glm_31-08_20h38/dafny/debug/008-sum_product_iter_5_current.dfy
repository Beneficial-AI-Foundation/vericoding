function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

// <vc-helpers>
lemma sum_prod_append(s: seq<int>, x: int)
    ensures sum(s + [x]) == sum(s) + x
    ensures prod(s + [x]) == prod(s) * x
{
    if |s| == 0 {
        calc {
            sum([] + [x]);
            == sum([x]);
            == x;
            == 0 + x;
            == sum([]) + x;
        }
        calc {
            prod([] + [x]);
            == prod([x]);
            == x;
            == 1 * x;
            == prod([]) * x;
        }
    } else {
        assert s[0] == s[0];
        assert s + [x] == [s[0]] + (s[1..] + [x]);
        calc {
            sum(s + [x]);
            == s[0] + sum(s[1..] + [x]);
            == s[0] + (sum(s[1..]) + x);
            == (s[0] + sum(s[1..])) + x;
            == sum(s) + x;
        }
        calc {
            prod(s + [x]);
            == s[0] * prod(s[1..] + [x]);
            == s[0] * (prod(s[1..]) * x);
            == (s[0] * prod(s[1..])) * x;
            == prod(s) * x;
        }
    }
}

lemma sum_prod_slice(numbers: seq<int>, i: int)
    requires 0 <= i < |numbers|
    ensures sum(numbers[0..i+1]) == sum(numbers[0..i]) + numbers[i]
    ensures prod(numbers[0..i+1]) == prod(numbers[0..i]) * numbers[i]
{
    sum_prod_append(numbers[0..i], numbers[i]);
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
    var n := |numbers|;
    s := 0;
    p := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant s == sum(numbers[0..i])
        invariant p == prod(numbers[0..i])
    {
        sum_prod_slice(numbers, i);
        s := s + numbers[i];
        p := p * numbers[i];
        i := i + 1;
    }
    assert numbers[0..n] == numbers;
}
// </vc-code>

