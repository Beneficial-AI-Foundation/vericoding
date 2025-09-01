function sumc(s: seq<int>, p: seq<bool>) : int
    requires |s| == |p|
    {
        if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
    }
function add_conditon(lst: seq<int>) : (p : seq<bool>)
    ensures |lst| == |p|
    {
        seq(|lst|, i requires 0 <= i < |lst| => i % 2 == 1 && lst[i] % 2 == 0)
    }

// <vc-helpers>
function add_condition_func(i: int, lst: seq<int>): bool
    requires 0 <= i < |lst|
{
    i % 2 == 1 && lst[i] % 2 == 0
}

lemma AddConditionLemma(lst: seq<int>)
    ensures add_conditon(lst) == seq(|lst|, i requires 0 <= i < |lst| => add_condition_func(i, lst))
{
    // Lemma to show that add_conditon is equivalent to constructing the sequence using add_condition_func
}

lemma SumcProperty(s: seq<int>, p: seq<bool>, i: int)
    requires 0 <= i <= |s|
    requires |s| == |p|
    ensures sumc(s[i..], p[i..]) == calculate_sum_from_index(s, p, i)
    decreases |s| - i
{
    if i == |s| {
        assert sumc(s[i..], p[i..]) == 0;
        assert calculate_sum_from_index(s, p, i) == 0;
    } else {
        assert calculate_sum_from_index(s, p, i) == (if p[i] then s[i] else 0) + calculate_sum_from_index(s, p, i + 1);
        SumcProperty(s, p, i + 1);
    }
}

function calculate_sum_from_index(s: seq<int>, p: seq<bool>, i: int): int
    requires 0 <= i <= |s|
    requires |s| == |p|
    decreases |s| - i
{
    if i == |s| then 0
    else (if p[i] then s[i] else 0) + calculate_sum_from_index(s, p, i + 1)
}
// </vc-helpers>

// <vc-spec>
method add(v: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sumc(v, add_conditon(v))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var s := 0;
    var p_seq := add_conditon(v);
    var i := 0;

    while i < |v|
        invariant 0 <= i <= |v|
        invariant s == calculate_sum_from_index(v, p_seq, 0) - calculate_sum_from_index(v, p_seq, i)
        invariant |v| == |p_seq|
        decreases |v| - i
    {
        if p_seq[i] {
            s := s + v[i];
        } else {
            s := s + 0;
        }
        i := i + 1;
    }

    SumcProperty(v, p_seq, 0);

    r := s;
}
// </vc-code>

// pure-end