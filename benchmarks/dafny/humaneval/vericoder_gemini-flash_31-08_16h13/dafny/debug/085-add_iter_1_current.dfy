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
    reads lst
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

    // We can prove p_seq is correctly constructed by add_conditon_func
    // Since add_conditon_func describes the condition for each element

    while i < |v|
        invariant 0 <= i <= |v|
        invariant s == calculate_sum_from_index(v, p_seq, 0) - calculate_sum_from_index(v, p_seq, i)
        // This invariant means s stores the sum of (p_seq[k] ? v[k] : 0) for k from 0 to i-1
        // which is equivalent to sumc(v[0..i],p_seq[0..i]) but using the helper calculate_sum_from_index
    {
        if p_seq[i] {
            s := s + v[i];
        } else {
            s := s + 0; // Explicitly adding 0 for clarity, can be removed
        }
        i := i + 1;
    }
    // After the loop, i == |v|.
    // So the invariant becomes s == calculate_sum_from_index(v, p_seq, 0) - calculate_sum_from_index(v, p_seq, |v|)
    // Since calculate_sum_from_index(v, p_seq, |v|) is 0, we have s == calculate_sum_from_index(v, p_seq, 0)

    // Prove that calculate_sum_from_index(v, p_seq, 0) is equal to sumc(v, p_seq)
    // using the SumcProperty lemma with i = 0.
    SumcProperty(v, p_seq, 0);

    r := s;
}
// </vc-code>

// pure-end