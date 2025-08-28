function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end
lemma sum_prop(s: seq<int>)
    requires |s| > 0
    ensures sum(s) == sum(s[..|s| - 1]) + s[ |s| - 1 ]
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}
// pure-end
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}
// pure-end
lemma prod_prop(s: seq<int>)
    requires |s| > 0
    ensures prod(s) == prod(s[..|s| - 1]) * s[ |s| - 1 ]
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}
// pure-end
method sum_product(numbers: seq<int>) returns (s : int, p : int)
    // post-condition-start
    ensures s == sum(numbers)
    ensures p == prod(numbers)
    // post-condition-end
 {
    // impl-start
    assert numbers[..|numbers|] == numbers; // assert-line
    s := 0;
    p := 1;
    for i := 0 to |numbers|
        // invariants-start
        invariant s == sum(numbers[..i])
        invariant p == prod(numbers[..i])
        // invariants-end
    {
        // assert-start
        assert sum(numbers[..i + 1]) == sum(numbers[..i]) + numbers[i] by {
            assert numbers[..i+1][..i] == numbers[..i]; // assert-line
            sum_prop(numbers[..i + 1]);
        }
        // assert-end
        s := s + numbers[i];

        // assert-start
        assert prod(numbers[..i + 1]) == prod(numbers[..i]) * numbers[i] by {
            assert numbers[..i+1][..i] == numbers[..i]; // assert-line
            prod_prop(numbers[..i + 1]);
        }
        // assert-end
        p := p * numbers[i];
    }

    return s, p;
    // impl-end
}
