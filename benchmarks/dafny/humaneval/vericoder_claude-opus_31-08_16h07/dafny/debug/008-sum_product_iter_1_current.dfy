function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

// <vc-helpers>
lemma sum_prop(s: seq<int>)
    requires |s| > 0
    ensures sum(s) == sum(s[..|s|-1]) + s[|s|-1]
{
    if |s| == 1 {
        assert s[..|s|-1] == s[..0] == [];
        assert sum(s[..|s|-1]) == 0;
        assert s[0] == s[|s|-1];
    } else {
        assert s[1..][..|s[1..]|-1] == s[1..|s|-1];
    }
}

lemma prod_prop(s: seq<int>)
    requires |s| > 0
    ensures prod(s) == prod(s[..|s|-1]) * s[|s|-1]
{
    if |s| == 1 {
        assert s[..|s|-1] == s[..0] == [];
        assert prod(s[..|s|-1]) == 1;
        assert s[0] == s[|s|-1];
    } else {
        assert s[1..][..|s[1..]|-1] == s[1..|s|-1];
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
        s := s + numbers[i];
        p := p * numbers[i];
        
        sum_prop(numbers[..i+1]);
        assert numbers[..i+1][..i] == numbers[..i];
        
        prod_prop(numbers[..i+1]);
        assert numbers[..i+1][..i] == numbers[..i];
        
        i := i + 1;
    }
    
    assert numbers[..|numbers|] == numbers;
}
// </vc-code>

