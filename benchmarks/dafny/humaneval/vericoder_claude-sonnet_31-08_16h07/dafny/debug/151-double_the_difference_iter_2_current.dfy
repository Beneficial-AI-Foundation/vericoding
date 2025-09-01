function sumc(s: seq<int>, p: seq<bool>) : int
    requires |s| == |p|
    {
        if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
    }
function add_conditon(lst: seq<int>) : (p : seq<bool>)
    ensures |lst| == |p|
    {
        seq(|lst|, i requires 0 <= i < |lst| => lst[i] >= 0 && lst[i] % 2 == 1)
    }
function square_seq(lst: seq<int>) : (sq : seq<int>)
        ensures |sq| == |lst|
        ensures forall i :: 0 <= i < |lst| ==> sq[i] == lst[i] * lst[i]
    {
        seq(|lst|, i requires 0 <= i < |lst| => lst[i] * lst[i])
    }

// <vc-helpers>
lemma sumc_append(s1: seq<int>, s2: seq<int>, p1: seq<bool>, p2: seq<bool>)
    requires |s1| == |p1| && |s2| == |p2|
    ensures sumc(s1 + s2, p1 + p2) == sumc(s1, p1) + sumc(s2, p2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert p1 + p2 == p2;
    } else {
        assert (s1 + s2)[1..] == s1[1..] + s2;
        assert (p1 + p2)[1..] == p1[1..] + p2;
        sumc_append(s1[1..], s2, p1[1..], p2);
    }
}

lemma sumc_single(s: int, p: bool)
    ensures sumc([s], [p]) == (if p then s else 0)
{
}

lemma square_seq_single(x: int)
    ensures square_seq([x]) == [x * x]
{
}

lemma add_conditon_single(x: int)
    ensures add_conditon([x]) == [x >= 0 && x % 2 == 1]
{
}

lemma square_seq_decomp(lst: seq<int>)
    requires |lst| > 0
    ensures square_seq(lst) == [lst[0] * lst[0]] + square_seq(lst[1..])
{
}

lemma add_conditon_decomp(lst: seq<int>)
    requires |lst| > 0
    ensures add_conditon(lst) == [lst[0] >= 0 && lst[0] % 2 == 1] + add_conditon(lst[1..])
{
}

lemma sumc_decomp(lst: seq<int>)
    requires |lst| > 0
    ensures sumc(square_seq(lst), add_conditon(lst)) == 
            sumc([lst[0] * lst[0]], [lst[0] >= 0 && lst[0] % 2 == 1]) + 
            sumc(square_seq(lst[1..]), add_conditon(lst[1..]))
{
    square_seq_decomp(lst);
    add_conditon_decomp(lst);
    sumc_append([lst[0] * lst[0]], square_seq(lst[1..]), 
                [lst[0] >= 0 && lst[0] % 2 == 1], add_conditon(lst[1..]));
}
// </vc-helpers>

// <vc-spec>
method double_the_difference(lst: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sumc(square_seq(lst), add_conditon(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if |lst| == 0 {
        r := 0;
        return;
    }
    
    var head := lst[0];
    var tail := lst[1..];
    
    var tail_result := double_the_difference(tail);
    
    var head_squared := head * head;
    var head_condition := head >= 0 && head % 2 == 1;
    var head_contribution := if head_condition then head_squared else 0;
    
    r := head_contribution + tail_result;
    
    sumc_single(head_squared, head_condition);
    sumc_decomp(lst);
}
// </vc-code>

