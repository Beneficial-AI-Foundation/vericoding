function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

// <vc-helpers>
lemma sum_append_lemma(s: seq<int>, x: int)
    ensures sum(s + [x]) == sum(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert sum([x]) == x + sum([]) == x + 0 == x;
        assert sum(s) + x == 0 + x == x;
    } else {
        assert s + [x] == [s[0]] + (s[1..] + [x]);
        assert sum(s + [x]) == s[0] + sum(s[1..] + [x]);
        sum_append_lemma(s[1..], x);
        assert sum(s[1..] + [x]) == sum(s[1..]) + x;
        assert sum(s + [x]) == s[0] + sum(s[1..]) + x == sum(s) + x;
    }
}

lemma prod_append_lemma(s: seq<int>, x: int)
    ensures prod(s + [x]) == prod(s) * x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert prod([x]) == x * prod([]) == x * 1 == x;
        assert prod(s) * x == 1 * x == x;
    } else {
        assert s + [x] == [s[0]] + (s[1..] + [x]);
        assert prod(s + [x]) == s[0] * prod(s[1..] + [x]);
        prod_append_lemma(s[1..], x);
        assert prod(s[1..] + [x]) == prod(s[1..]) * x;
        assert prod(s + [x]) == s[0] * prod(s[1..]) * x == prod(s) * x;
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
    s := 0;
    p := 1;
    
    var i := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant s == sum(numbers[..i])
        invariant p == prod(numbers[..i])
    {
        assert numbers[..i+1] == numbers[..i] + [numbers[i]];
        sum_append_lemma(numbers[..i], numbers[i]);
        prod_append_lemma(numbers[..i], numbers[i]);
        s := s + numbers[i];
        p := p * numbers[i];
        i := i + 1;
    }
    assert i == |numbers|;
    assert numbers[..i] == numbers[..|numbers|] == numbers;
}
// </vc-code>
